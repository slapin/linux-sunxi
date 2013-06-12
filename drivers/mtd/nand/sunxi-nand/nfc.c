/*
 * nfc.c
 *
 * Copyright (C) 2013 Qiang Yu <yuq825@gmail.com>
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

#include <linux/io.h>
#include <linux/module.h>
#include <linux/string.h>
#include <linux/mtd/mtd.h>
#include <linux/mtd/nand.h>
#include <linux/slab.h>
#include <linux/interrupt.h>
#include <linux/dma-mapping.h>
#include <plat/sys_config.h>
#include <linux/delay.h>
#include "defs.h"
#include "regs.h"
#include "dma.h"
#include "nand_id.h"

// do we need to consider exclusion of offset?
// it should be in high level that the nand_chip ops have been
// performed with exclusion already
// find it is:
//   nand_get_device() & nand_release_device()
// 
static int read_offset = 0;
static int write_offset = 0;
static char *read_buffer = NULL;
static char *write_buffer = NULL;
static int buffer_size = 8192 + 448;
static dma_addr_t read_buffer_dma;
static dma_addr_t write_buffer_dma;
static int dma_hdle;
static struct nand_ecclayout sunxi_ecclayout;
static DECLARE_WAIT_QUEUE_HEAD(nand_rb_wait);
static int program_column = -1, program_page = -1;
uint32_t pioc_handle;

unsigned int hwecc_switch = 1;
module_param(hwecc_switch, uint, 0);
MODULE_PARM_DESC(hwecc_switch, "hardware ECC switch, 1=on, 0=off");

unsigned int use_flash_bbt = 1;
module_param(use_flash_bbt, uint, 0);
MODULE_PARM_DESC(use_flash_bbt, "use flash bad block table, 1=use, 0=not");

unsigned int random_seed = 0x4a80;
module_param(random_seed, uint, 0);
MODULE_PARM_DESC(random_seed, "random seed used");

//////////////////////////////////////////////////////////////////
// SUNXI platform
//

// Get clock rate from PLL5
static uint32_t sunxi_get_pll5_clk(void)
{
	uint32_t reg_val;
	uint32_t div_p, factor_n;
	uint32_t factor_k, factor_m;
	uint32_t clock;

	reg_val = readl(PLL5_CFG_REG);
	DBG_INFO("PLL5_CFG_REG is 0x%x \n", reg_val);
	div_p = (reg_val & PLL5_OUT_EXT_DIV_P_MASK) >> PLL5_OUT_EXT_DIV_P_SHIFT;
	DBG_INFO("div_p is %d \n", div_p);
	factor_n = (reg_val & PLL5_FACTOR_N_MASK) >> PLL5_FACTOR_N_SHIFT;
	DBG_INFO("factor_n is %d \n", factor_n);
	factor_k = ((reg_val & PLL5_FACTOR_K_MASK) >> PLL5_FACTOR_K_SHIFT) + 1;
	DBG_INFO("factor_k is %d \n", factor_k);
	factor_m = ((reg_val & PLL5_FACTOR_M_MASK) >> PLL5_FACTOR_M_SHIFT) + 1;
	DBG_INFO("factor_m is %d \n", factor_m);

	clock = 24 * factor_n * factor_k / div_p / factor_m;
	DBG_INFO("cmu_clk is %d \n", clock);

	return clock;
}

static void sunxi_set_nand_clock(uint32_t nand_max_clock)
{
	uint32_t edo_clk, cmu_clk;
	uint32_t cfg;
	uint32_t nand_clk_divid_ratio;

	// open ahb nand clk (bus clock for CPU access)
	cfg = readl(AHB_GATING_REG0);
	DBG_INFO("Setting NAND clock ... read AHB_GATING_REG0 is 0x%x \n", cfg);
	cfg |= 1 << AHB_GATING_NAND_CLK_SHIFT;
	writel(cfg, AHB_GATING_REG0);
	DBG_INFO("Setting NAND clock ... written AHB_GATING_REG0 is 0x%x \n",
		 cfg);

	// set nand clock (device clock for NFC running)
	edo_clk = nand_max_clock * 2;
	DBG_INFO("Setting NAND clock ... edo_clk is %d \n", edo_clk);

	cmu_clk = sunxi_get_pll5_clk();
	nand_clk_divid_ratio = cmu_clk / edo_clk;
	if (cmu_clk % edo_clk)
		nand_clk_divid_ratio++;
	if (nand_clk_divid_ratio) {
		if (nand_clk_divid_ratio > 16)
			nand_clk_divid_ratio = 15;
		else
			nand_clk_divid_ratio--;
	}
	DBG_INFO("Setting NAND clock ... nand_clk_divid_ratio is %d \n",
		 nand_clk_divid_ratio);

	// set nand clock gate on
	cfg = readl(NAND_SCLK_CFG_REG);
	DBG_INFO("Setting NAND clock ... read NAND_SCLK_CFG_REG is 0x%x \n",
		 cfg);
	// gate on nand clock
	cfg |= 1 << SCLK_GATING_SHIFT;
	// take cmu pll as nand src block
	cfg &= ~CLK_SRC_SEL_MASK;
	cfg |= 0x2 << CLK_SRC_SEL_SHIFT;
	// set divn = 0
	cfg &= ~CLK_DIV_RATIO_N_MASK;
	// set divm
	cfg &= ~CLK_DIV_RATIO_M_MASK;
	cfg |=
	    (nand_clk_divid_ratio << CLK_DIV_RATIO_M_SHIFT) &
	    CLK_DIV_RATIO_M_MASK;
	writel(cfg, NAND_SCLK_CFG_REG);
	DBG_INFO("Setting NAND clock ... written NAND_SCLK_CFG_REG is 0x%x \n",
		 cfg);
}

static void release_nand_clock(void)
{
	uint32_t cfg;

	// disable bus clock
	cfg = readl(AHB_GATING_REG0);
	DBG_INFO("Releasing NADND clock ... read AHB_GATING_REG0 is 0x%x \n",
		 cfg);
	cfg &= ~(1 << AHB_GATING_NAND_CLK_SHIFT);
	writel(cfg, AHB_GATING_REG0);
	DBG_INFO("Releasing NADND clock ... written AHB_GATING_REG0 is 0x%x \n",
		 cfg);

	// disable device clock
	cfg = readl(NAND_SCLK_CFG_REG);
	DBG_INFO("Releasing NAND clock ... read NAND_SCLK_CFG_REG is 0x%x \n",
		 cfg);
	cfg &= ~(1 << SCLK_GATING_SHIFT);
	writel(cfg, NAND_SCLK_CFG_REG);
	DBG_INFO
	    ("Releasing NAND clock ... written NAND_SCLK_CFG_REG is 0x%x \n",
	     cfg);
}

/* is not used
static void active_nand_clock(void)
{
	uint32_t cfg;

	// disable bus clock
	cfg = readl(AHB_GATING_REG0);
	DBG_INFO("Activating NAND clock ... read AHB_GATING_REG0 is 0x%x \n",
		 cfg);
	cfg |= 1 << AHB_GATING_NAND_CLK_SHIFT;
	writel(cfg, AHB_GATING_REG0);
	DBG_INFO("Activating NAND clock ... written AHB_GATING_REG0 is 0x%x \n",
		 cfg);

	// disable device clock
	cfg = readl(NAND_SCLK_CFG_REG);
	DBG_INFO("Activating NAND clock ... read NAND_SCLK_CFG_REG is 0x%x \n",
		 cfg);
	cfg |= 1 << SCLK_GATING_SHIFT;
	writel(cfg, NAND_SCLK_CFG_REG);
	DBG_INFO
	    ("Activating NAND clock ... written NAND_SCLK_CFG_REG is 0x%x \n",
	     cfg);
}*/

// Set PIOC pin for NAND Flash use
static void sunxi_set_nand_pio(void)
{
	pioc_handle = gpio_request_ex("nand_para", NULL);
	if (pioc_handle) {
		DBG_INFO("Got NAND PIO\n");
	} else {
		ERR_INFO("Could not get NAND PIO!\n");
	}
}

static void sunxi_release_nand_pio(void)
{
	DBG_INFO("nand gpio_release\n");
	gpio_release(pioc_handle, 1);
}

/////////////////////////////////////////////////////////////////
// Utils
//

static inline void wait_cmdfifo_free(void)
{
	int timeout = 0xffffff;
	DBG_INFO("Waiting for command FIFO to be free");
	while ((timeout--) && (readl(NFC_REG_ST) & NFC_CMD_FIFO_STATUS)) ;
	if (timeout <= 0) {
		ERR_INFO("Wait for command FIFO timeout!\n");
	}
}

static inline void wait_cmd_finish(void)
{
	int timeout = 0xffffff;
	DBG_INFO("Waiting for command to be finished");
	while ((timeout--) && !(readl(NFC_REG_ST) & NFC_CMD_INT_FLAG)) ;
	if (timeout <= 0) {
		ERR_INFO("Wait for command finish timeout!\n");
		return;
	}
	writel(NFC_CMD_INT_FLAG, NFC_REG_ST);
}

static void select_rb(int rb)
{
	uint32_t ctl;
	// A10 has 2 RB pin
	DBG_INFO("Selecting RB ... RB is %d \n", rb);
	ctl = readl(NFC_REG_CTL);
	DBG_INFO("Selecting RB ... read NFC_REG_CTL is 0x%x \n", ctl);
	ctl &= ((~NFC_RB_SEL) & 0xffffffff);
	ctl |= ((rb & 0x1) << 3);
	writel(ctl, NFC_REG_CTL);
	DBG_INFO("Selecting RB ... written NFC_REG_CTL is 0x%x \n", ctl);
	//udelay(60);
}

// 1 for ready, 0 for not ready
static inline int check_rb_ready(int rb)
{
	return (readl(NFC_REG_ST) & (NFC_RB_STATE0 << (rb & 0x3))) ? 1 : 0;
}

static void enable_random(void)
{
	uint32_t ctl;
	ctl = readl(NFC_REG_ECC_CTL);
	DBG_INFO("Enabling random ... read NFC_REG_ECC_CTL is 0x%x \n", ctl);
	ctl |= NFC_RANDOM_EN;
	ctl &= ~NFC_RANDOM_DIRECTION;
	ctl &= ~NFC_RANDOM_SEED;
	ctl |= (random_seed << 16);
	writel(ctl, NFC_REG_ECC_CTL);
	DBG_INFO("Enabling random ... written NFC_REG_ECC_CTL is 0x%x \n", ctl);
}

static void disable_random(void)
{
	uint32_t ctl;
	ctl = readl(NFC_REG_ECC_CTL);
	DBG_INFO("Disabling random ... read NFC_REG_ECC_CTL is 0x%x \n", ctl);
	ctl &= ~NFC_RANDOM_EN;
	writel(ctl, NFC_REG_ECC_CTL);
	DBG_INFO("Disabling random ... written NFC_REG_ECC_CTL is 0x%x \n",
		 ctl);
}

static void enable_ecc(int pipline)
{
	uint32_t cfg = readl(NFC_REG_ECC_CTL);
	DBG_INFO("Enabling ECC mode ... read NFC_REG_ECC_CTL is 0x%x \n", cfg);
	DBG_INFO("Enabling ECC mode ... ECC pipeline is %d \n", pipline);
	if (pipline)
		cfg |= NFC_ECC_PIPELINE;
	else
		cfg &= (~NFC_ECC_PIPELINE) & 0xffffffff;

	// if random open, disable exception
	if (cfg & (1 << 9)) {
		DBG_INFO
		    ("Enabling ECC mode ... random is open, disabling ECC exception");
		cfg &= ~(0x1 << 4);
	} else
		cfg |= 1 << 4;

	//cfg |= 30; //16 bit ecc

	cfg |= NFC_ECC_EN;
	writel(cfg, NFC_REG_ECC_CTL);
	DBG_INFO("Enabling ECC mode ... written NFC_REG_ECC_CTL is 0x%x \n",
		 cfg);
}

static void set_ecc_mode(int mode)
{
	uint32_t ctl;
	ctl = readl(NFC_REG_ECC_CTL);
	DBG_INFO("Setting ECC mode ... read NFC_REG_ECC_CTL is 0x%x \n", ctl);
	ctl &= ~NFC_ECC_MODE;
	ctl |= mode << NFC_ECC_MODE_SHIFT;
	writel(ctl, NFC_REG_ECC_CTL);
	DBG_INFO("Setting ECC mode ... written NFC_REG_ECC_CTL is 0x%x \n",
		 ctl);
}

int check_ecc(int eblock_cnt)
{
	int i;
	int ecc_mode;
	int max_ecc_bit_cnt;
	int cfg, corrected = 0;

	ecc_mode =
	    ((readl(NFC_REG_ECC_CTL) & NFC_ECC_MODE) >> NFC_ECC_MODE_SHIFT);

	switch (ecc_mode) {
	case 0:
		max_ecc_bit_cnt = 16;
		break;
	case 1:
		max_ecc_bit_cnt = 24;
		break;
	case 2:
		max_ecc_bit_cnt = 28;
		break;
	case 3:
		max_ecc_bit_cnt = 32;
		break;
	case 4:
		max_ecc_bit_cnt = 40;
		break;
	case 5:
		max_ecc_bit_cnt = 48;
		break;
	case 6:
		max_ecc_bit_cnt = 56;
		break;
	case 7:
		max_ecc_bit_cnt = 60;
		break;
	case 8:
		max_ecc_bit_cnt = 64;
		break;
	default:
		BUG();
	}

	DBG_INFO("Checking ECC ... eraseblock count is %d \n", eblock_cnt);
	DBG_INFO("Checking ECC ... ECC mode is 0x%x \n", ecc_mode);
	DBG_INFO
	    ("Checking ECC ... maximum bits that can be corrected by ECC: %d \n",
	     max_ecc_bit_cnt);

	//check ecc error
	cfg = readl(NFC_REG_ECC_ST) & 0xffff;
	DBG_INFO("Checking ECC ... NFC_REG_ECC_ST & 0xffff is 0x%x \n", cfg);
	for (i = 0; i < eblock_cnt; i++) {
		if (cfg & (1 << i)) {
			ERR_INFO
			    ("ECC status reports too many errors at eraseblock %d! \n",
			     i);
			return -1;
		}
	}

	//check ecc limit
	for (i = 0; i < eblock_cnt; i += 4) {
		int j, n = (eblock_cnt - i) < 4 ? (eblock_cnt - i) : 4;
		cfg = readl(NFC_REG_ECC_CNT0 + i);
		DBG_INFO("Checking ECC ... NFC_REG_ECC_CNT0 + i 0x%x \n", cfg);
		for (j = 0; j < n; j++, cfg >>= 8) {
			int bits = cfg & 0xff;
			if (bits >= max_ecc_bit_cnt - 4) {
				DBG_INFO("ECC limit %d/%d\n", bits,
					 max_ecc_bit_cnt);
				corrected++;
			}
		}
	}

	return corrected;
}

static void disable_ecc(void)
{
	uint32_t cfg = readl(NFC_REG_ECC_CTL);
	DBG_INFO("Disabling ECC ... NFC_REG_ECC_CTL is 0x%x \n", cfg);
	cfg &= ((~NFC_ECC_EN) & 0xffffffff);
	writel(cfg, NFC_REG_ECC_CTL);
	DBG_INFO("Disabling ECC ... NFC_REG_ECC_CTL is 0x%x \n", cfg);
}

/////////////////////////////////////////////////////////////////
// NFC
//

static void nfc_select_chip(struct mtd_info *mtd, int chip)
{
	uint32_t ctl;
	switch (chip) {
	case -1:
		/* do nothing ? wrong CS sent?
		   if this is enabled - MTD layer in 3.4 selects wrong chip
		   after nfc_first_init() and before nfc_second_init() */
		break;
	case 0:		/* fall down and transfer CS number to NFC_CE_SEL register */
	case 1:
/* SUN5I can do only 2 chip selects */
#if defined CONFIG_ARCH_SUN4I
	case 2:
	case 3:
	case 4:
	case 5:
	case 6:
	case 7:
#endif
		DBG_INFO("ChipSelect ... chip is %d \n", chip);
		ctl = readl(NFC_REG_CTL);
		DBG_INFO("ChipSelect... read NFC_REG_CTL is 0x%x \n", ctl);
		ctl &= ((~NFC_CE_SEL) & 0xffffffff);
		ctl |= ((chip & 7) << 24);
		writel(ctl, NFC_REG_CTL);
		DBG_INFO("ChipSelect... written NFC_REG_CTL is 0x%x \n", ctl);
		break;
	default:
		/* SUN4I can do only 8 chip selects 
		   if more requested - MTD layer did something horribly wrong */
		BUG();
	}
}

static void nfc_cmdfunc(struct mtd_info *mtd, unsigned command, int column,
			int page_addr)
{
	int i;
	uint32_t cfg = command;
	int read_size, write_size, do_enable_ecc = 0;
	int addr_cycle, wait_rb_flag, byte_count, sector_count;
	addr_cycle = wait_rb_flag = byte_count = sector_count = 0;

	DBG_INFO("-------------------------------------- \n");
	DBG_INFO("Recieved command 0x%X ...\n", command);
	DBG_INFO("Recieved column 0x%X ...\n", column);
	DBG_INFO("Recieved page_addr 0x%X ...\n", page_addr);

	wait_cmdfifo_free();

	// switch to AHB
	writel(readl(NFC_REG_CTL) & ~NFC_RAM_METHOD, NFC_REG_CTL);

	switch (command) {
	case NAND_CMD_RESET:
	case NAND_CMD_ERASE2:
		break;
	case NAND_CMD_READID:
		DBG_INFO(">>> Recieved READID command \n");
		addr_cycle = 1;
		// read 8 byte ID
		byte_count = 8;
		break;
	case NAND_CMD_PARAM:
		DBG_INFO(">>> Recieved CMD_PARAM command \n");
		addr_cycle = 1;
		byte_count = 1024;
		wait_rb_flag = 1;
		break;
	case NAND_CMD_RNDOUT:
		DBG_INFO(">>> Recieved CMD_RNDOUT command \n");
		addr_cycle = 2;
		writel(0xE0, NFC_REG_RCMD_SET);
		byte_count = mtd->oobsize;
		cfg |= NFC_SEQ | NFC_SEND_CMD2;
		wait_rb_flag = 1;
		break;
	case NAND_CMD_READOOB:
	case NAND_CMD_READ0:
		DBG_INFO("MTD Write size is %d \n", mtd->writesize);
		if (command == NAND_CMD_READOOB) {
			DBG_INFO(">>> Recieved READOOB command \n");
			cfg = NAND_CMD_READ0;
			// sector num to read
			sector_count = 1;
			read_size = 1024;
			// OOB offset
			column += mtd->writesize;
		} else {
			DBG_INFO(">>> READ0 command part 1");
			sector_count = mtd->writesize / 1024;
			read_size = mtd->writesize;
			do_enable_ecc = 1;
			DBG_INFO("cmdfunc read %d %d\n", column, page_addr);
		}

		//access NFC internal RAM by DMA bus
		writel(readl(NFC_REG_CTL) | NFC_RAM_METHOD, NFC_REG_CTL);

		// if the size is smaller than NFC_REG_SECTOR_NUM, read command won't finish
		// does that means the data read out (by DMA through random data output) hasn't finish?
		/* this also means that if you have FIFO or command timeout - you possibly trying to read wrong amount of data */
		DBG_INFO("NFC_REG_SECTOR_NUM is: %d \n",
			 readl(NFC_REG_SECTOR_NUM));
		DBG_INFO("read buffer size is: %d", sizeof(read_buffer));
		DBG_INFO("read size is: %d", read_size);

		dma_nand_config_start(dma_hdle, 0, (uint32_t) read_buffer,
				      read_size);
		addr_cycle = 5;
		// NFC RAM0 is 1K size
		byte_count = 1024;
		wait_rb_flag = 1;
		// 0x30 for 2nd cycle of read page
		// 0x05+0xe0 is the random data output command
		writel(0x00e00530, NFC_REG_RCMD_SET);
		// NFC_SEND_CMD1 for the command 1nd cycle enable
		// NFC_SEND_CMD2 for the command 2nd cycle enable
		// NFC_SEND_CMD3 & NFC_SEND_CMD4 for NFC_READ_CMD0 & NFC_READ_CMD1
		cfg |= NFC_SEND_CMD2 | NFC_DATA_SWAP_METHOD;
		// 3 - ?
		// 2 - page command
		// 1 - spare command?
		// 0 - normal command

		/* FIXME this needs to be properly figured out in future */
		if (command == NAND_CMD_READOOB) {
			cfg |= 2 << 30;
		} else {
			cfg |= 2 << 30;
		}
		break;
	case NAND_CMD_ERASE1:
		addr_cycle = 3;
		DBG_INFO(">>> ERASE1 block 0x%X\n", page_addr);
		break;
	case NAND_CMD_SEQIN:
		program_column = column;
		program_page = page_addr;
		write_offset = 0;
		return;
	case NAND_CMD_PAGEPROG:
		DBG_INFO(">>> Recieved PAGEPROG command \n");
		cfg = NAND_CMD_SEQIN;
		addr_cycle = 5;
		column = program_column;
		page_addr = program_page;
		// for write OOB
		if (column == mtd->writesize) {
			DBG_INFO("Programming OOB page \n");
			sector_count = 1;
			write_size = 1024;
		} else if (column == 0) {
			DBG_INFO("Programming standard page \n");
			sector_count = mtd->writesize / 1024;
			do_enable_ecc = 1;
			write_size = mtd->writesize;
			for (i = 0; i < sector_count; i++) {
				writel(*
				       ((unsigned int *)(write_buffer +
							 mtd->writesize) + i),
				       NFC_REG_USER_DATA(i));
			}
		} else {
			ERR_INFO("Wrong column and page address %d %d !",
				 column, page_addr);;
			BUG();
			return;
		}

		//access NFC internal RAM by DMA bus
		writel(readl(NFC_REG_CTL) | NFC_RAM_METHOD, NFC_REG_CTL);
		dma_nand_config_start(dma_hdle, 1, (uint32_t) write_buffer,
				      write_size);
		// RAM0 is 1K size
		byte_count = 1024;
		writel(0x00008510, NFC_REG_WCMD_SET);
		cfg |= NFC_SEND_CMD2 | NFC_DATA_SWAP_METHOD | NFC_ACCESS_DIR;
		/* FIXME same as for reading - this needs to be fixed */
		if (column == mtd->writesize) {
			cfg |= 2 << 30;
		} else if (column == 0) {
			cfg |= 2 << 30;
		} else {
			ERR_INFO("Wrong column and page address %d %d !",
				 column, page_addr);
			BUG();
		}

		if (column != 0) {
			DBG_INFO("cmdfunc program %d %d with %x %x %x\n",
				 column, page_addr, write_buffer[0],
				 write_buffer[1], write_buffer[2]);
		}
		break;
	case NAND_CMD_STATUS:
		byte_count = 1;
		break;
	default:
		ERR_INFO("Recieved unknown command!\n");
		return;
	}

	// address cycle
	if (addr_cycle) {
		uint32_t low = 0;
		uint32_t high = 0;
		switch (addr_cycle) {
		case 2:
			low = column & 0xffff;
			DBG_INFO("in addr_cycle 2 low is 0x%X \n", low);
			break;
		case 3:
			low = page_addr & 0xffffff;
			DBG_INFO("in addr_cycle 3 low is 0x%X \n", low);
			break;
		case 5:
			high = (page_addr >> 16) & 0xff;
			DBG_INFO("in addr_cycle 5 high is 0x%X \n", high);
			/* fall through */
		case 4:
			low = (column & 0xffff) | (page_addr << 16);
			DBG_INFO("in addr_cycle 4 low is 0x%X \n", low);
			break;
		}
		DBG_INFO("address cycle low is 0x%X  \n", low);
		DBG_INFO("address cycle high is 0x%X  \n", high);
		writel(low, NFC_REG_ADDR_LOW);
		writel(high, NFC_REG_ADDR_HIGH);
		cfg |= NFC_SEND_ADR;
		cfg |= ((addr_cycle - 1) << 16);
		DBG_INFO("NFC_SEND_ADR in addr_cycle is 0x%X \n", cfg);
	}
	// command will wait until the RB ready to mark finish?
	if (wait_rb_flag)
		cfg |= NFC_WAIT_FLAG;

	// will fetch data
	if (byte_count) {
		cfg |= NFC_DATA_TRANS;
		DBG_INFO("byte_count is %d \n", byte_count);
		writel(byte_count, NFC_REG_CNT);
	}
	// set sectors
	if (sector_count) {
		DBG_INFO("sector_count is %d \n", sector_count);
		writel(sector_count, NFC_REG_SECTOR_NUM);
	}
	// enable ecc
	if (hwecc_switch && do_enable_ecc)
		/* ECC pipeline is sent in next function, but why, if it always is 1 ? */
		enable_ecc(1);

	// send command
	cfg |= NFC_SEND_CMD1;
	writel(cfg, NFC_REG_CMD);
	DBG_INFO(">>> Send command 0x%x to NFC_REG_CMD <<<\n", cfg);

	switch (command) {
	case NAND_CMD_READ0:
	case NAND_CMD_READOOB:
	case NAND_CMD_PAGEPROG:
		DBG_INFO("Waitng for NAND DMA to finish\n");
		dma_nand_wait_finish();
		break;
	}

	// wait command send complete
	wait_cmdfifo_free();
	wait_cmd_finish();

	// reset will wait for RB ready
	switch (command) {
	case NAND_CMD_RESET:
		DBG_INFO("Resetting NAND\n");
		// wait rb0 ready
		select_rb(0);
		while (!check_rb_ready(0)) ;
		// wait rb1 ready
		select_rb(1);
		while (!check_rb_ready(1)) ;
		// select rb 0 back
		select_rb(0);
		break;
	case NAND_CMD_READ0:
		DBG_INFO("READ0 command part 2 \n");
		for (i = 0; i < sector_count; i++) {
			*((unsigned int *)(read_buffer + mtd->writesize) + i) =
			    readl(NFC_REG_USER_DATA(i));
		}
		break;
	}

	if (hwecc_switch && do_enable_ecc)
		disable_ecc();

	DBG_INFO("Command 0x%X done\n", command);
	DBG_INFO("-----------------------------------------\n");

	// read write offset
	read_offset = 0;
}

static uint8_t nfc_read_byte(struct mtd_info *mtd)
{
	uint8_t data;
	data = readb(NFC_RAM0_BASE + read_offset++);
	DBG_INFO(">>> nfc_read_byte ... read_offset is 0x%X \n", read_offset);
	DBG_INFO(">>> nfc_read_byte ... read value of 0x%X \n", data);
	return data;
}

static int nfc_dev_ready(struct mtd_info *mtd)
{
	return check_rb_ready(0);
}

static void nfc_write_buf(struct mtd_info *mtd, const uint8_t * buf, int len)
{
	if (write_offset + len > buffer_size) {
		ERR_INFO("write too much offset=%d len=%d buffer size=%d\n",
			 write_offset, len, buffer_size);
		return;
	}
	memcpy(write_buffer + write_offset, buf, len);
	write_offset += len;
}

static void nfc_read_buf(struct mtd_info *mtd, uint8_t * buf, int len)
{
	if (read_offset + len > buffer_size) {
		ERR_INFO("read too much offset=%d len=%d buffer size=%d\n",
			 read_offset, len, buffer_size);
		return;
	}
	memcpy(buf, read_buffer + read_offset, len);
	read_offset += len;
}

static irqreturn_t nfc_interrupt_handler(int irq, void *dev_id)
{
	unsigned int st = readl(NFC_REG_ST);

	if (st & NFC_RB_B2R) {
		DBG_INFO("RB is back to READY state\n");
		wake_up(&nand_rb_wait);
	}
	if (st & NFC_CMD_INT_FLAG) {
		DBG_INFO("CMD INT\n");
	}
	if (st & NFC_DMA_INT_FLAG) {
		DBG_INFO("DMA INT\n");
	}
	if (st & NFC_NATCH_INT_FLAG) {
		DBG_INFO("NATCH INT\n");
	}
	// clear interrupt
	DBG_INFO("NFC_REG_ST is %X \n", st);
	writel(st, NFC_REG_ST);
	return IRQ_HANDLED;
}

static int get_chip_status(struct mtd_info *mtd)
{
	struct nand_chip *nand = mtd->priv;
	DBG_INFO("get_chip_status requested \n");
	nand->cmdfunc(mtd, NAND_CMD_STATUS, -1, -1);
	return nand->read_byte(mtd);
}

// For erase and program command to wait for chip ready
static int nfc_wait(struct mtd_info *mtd, struct nand_chip *chip)
{
	int err;
	DBG_INFO("nfc_wait requested\n");
	// clear B2R interrupt state
	writel(NFC_RB_B2R, NFC_REG_ST);

	if (check_rb_ready(0))
		goto out;

	// enable B2R interrupt
	writel(NFC_B2R_INT_ENABLE, NFC_REG_INT);
	if ((err =
	     wait_event_timeout(nand_rb_wait, check_rb_ready(0), 1 * HZ)) < 0) {
		DBG_INFO("nfc wait got exception %d\n", err);
	}
	// disable interrupt
	writel(0, NFC_REG_INT);

out:
	return get_chip_status(mtd);
}

static void nfc_ecc_hwctl(struct mtd_info *mtd, int mode)
{

}

static int nfc_ecc_calculate(struct mtd_info *mtd, const uint8_t * dat,
			     uint8_t * ecc_code)
{
	return 0;
}

static int nfc_ecc_correct(struct mtd_info *mtd, uint8_t * dat,
			   uint8_t * read_ecc, uint8_t * calc_ecc)
{
	if (!hwecc_switch)
		return 0;
	/* FIXME The following code checks wether it is intended check or not, problem is, our HWECC doesnt like this
	 * and even blank (!) pages go through ECC checking */

	/*uint8_t diff0, diff1, diff2, diff3;
	   uint32_t size, i;

	   size = sizeof(&read_ecc);
	   DBG_INFO("ECC Correct ... size of ecc is: %d", size);
	   diff0 = read_ecc[0] ^ calc_ecc[0];
	   diff1 = read_ecc[1] ^ calc_ecc[1];
	   diff2 = read_ecc[2] ^ calc_ecc[2];
	   diff3 = read_ecc[3] ^ calc_ecc[3];

	   DBG_INFO("ECC Correct ... diffs: 0x%X 0x%X 0x%X 0x%X \n", diff0, diff1, diff2, diff3);

	   for(i=0; i < sizeof(&read_ecc); i++)
	   {
	   DBG_INFO("ECC Correct ... read ecc: 0x%X calc ecc: 0x%X\n", read_ecc[i], calc_ecc[i]);
	   }

	   if (diff0 == 0 && diff1 == 0 && diff2 == 0 && diff3 == 0) {
	   DBG_INFO("ECC Correct ... There are no differences between pages needed checking! \n");
	   return 0;   
	   }

	   if (read_ecc[0] == 0xff && read_ecc[1] == 0xff && read_ecc[2] == 0xff && read_ecc[2] == 0xff)
	   {
	   DBG_INFO("ECC Correct ... Tried to check an empty page!\n");
	   return 0;
	   } */

	return check_ecc(mtd->writesize / 1024);
}

/* This is entirely untested! */
struct save_1k_mode {
	uint32_t ctl;
	uint32_t ecc_ctl;
	uint32_t spare_area;
};

static void enter_1k_mode(struct save_1k_mode *save)
{
	uint32_t ctl;

	ctl = readl(NFC_REG_CTL);
	save->ctl = ctl;
	ctl &= ~NFC_PAGE_SIZE;
	writel(ctl, NFC_REG_CTL);

	ctl = readl(NFC_REG_ECC_CTL);
	save->ecc_ctl = ctl;
	set_ecc_mode(8);

	ctl = readl(NFC_REG_SPARE_AREA);
	save->spare_area = ctl;
	writel(1024, NFC_REG_SPARE_AREA);
}

static void exit_1k_mode(struct save_1k_mode *save)
{
	writel(save->ctl, NFC_REG_CTL);
	writel(save->ecc_ctl, NFC_REG_ECC_CTL);
	writel(save->spare_area, NFC_REG_SPARE_AREA);
}

void nfc_read_page1k(uint32_t page_addr, void *buff)
{
	struct save_1k_mode save;
	uint32_t cfg =
	    NAND_CMD_READ0 | NFC_SEQ | NFC_SEND_CMD1 | NFC_DATA_TRANS |
	    NFC_SEND_ADR | NFC_SEND_CMD2 | ((5 - 1) << 16) | NFC_WAIT_FLAG |
	    NFC_DATA_SWAP_METHOD | (2 << 30);

	wait_cmdfifo_free();

	enter_1k_mode(&save);

	writel(readl(NFC_REG_CTL) | NFC_RAM_METHOD, NFC_REG_CTL);
	dma_nand_config_start(dma_hdle, 0, (uint32_t) buff, 1024);

	writel(page_addr << 16, NFC_REG_ADDR_LOW);
	writel(page_addr >> 16, NFC_REG_ADDR_HIGH);
	writel(1024, NFC_REG_CNT);
	writel(0x00e00530, NFC_REG_RCMD_SET);
	writel(1, NFC_REG_SECTOR_NUM);

	enable_random();
	if (hwecc_switch)
		enable_ecc(1);

	writel(cfg, NFC_REG_CMD);

	dma_nand_wait_finish();
	wait_cmdfifo_free();
	wait_cmd_finish();

	if (hwecc_switch) {
		disable_ecc();
		check_ecc(1);
	}
	disable_random();

	exit_1k_mode(&save);
}

/*
static void first_test_nfc(struct mtd_info *mtd)
{
	nfc_cmdfunc(mtd, NAND_CMD_RESET, -1, -1);
	DBG_INFO("reset\n");
	DBG_INFO("nand ctrl %x\n", readl(NFC_REG_CTL));
	DBG_INFO("nand ecc ctrl %x\n", readl(NFC_REG_ECC_CTL));
	DBG_INFO("nand timing %x\n", readl(NFC_REG_TIMING_CTL));
	nfc_cmdfunc(mtd, NAND_CMD_READID, 0, -1);
	DBG_INFO("readid first time: %x %x\n", 
			 nfc_read_byte(mtd),  nfc_read_byte(mtd));
	nfc_cmdfunc(mtd, NAND_CMD_READID, 0, -1);
	DBG_INFO("readid second time: %x %x\n", 
			 nfc_read_byte(mtd),  nfc_read_byte(mtd));
}
*/

int nfc_first_init(struct mtd_info *mtd)
{
	uint32_t ctl;
	struct nand_chip *nand = mtd->priv;

	if (hwecc_switch) {
		DBG_INFO("hardware ECC is on\n");
	} else {
		DBG_INFO("hardware ECC is off\n");
	}

	if (use_flash_bbt) {
		DBG_INFO("use flash bad block table\n");
	} else {
		DBG_INFO("not use flash bad block table\n");
	}

	DBG_INFO("random_seed = %x\n", random_seed);

	// set NFC clock source
	sunxi_set_nand_clock(20);

	// set NFC pio
	sunxi_set_nand_pio();

	// reset NFC
	ctl = readl(NFC_REG_CTL);
	DBG_INFO("Resetiing NFC... NFC_REG_CTL 0x%x\n", ctl);
	ctl |= NFC_RESET;
	DBG_INFO("Resetiing NFC... NFC_RESET 0x%x\n", ctl);

	writel(ctl, NFC_REG_CTL);
	while (readl(NFC_REG_CTL) & NFC_RESET) ;

	// enable NFC
	//ctl = 0; 
	ctl |= NFC_EN;
	DBG_INFO("Enabling NFC... NFC_REG_CTL 0x%x\n", ctl);
	writel(ctl, NFC_REG_CTL);

	// serial_access_mode = 1
	// this is needed by some nand chip to read ID
	//ctl = 0;
	ctl = (1 << 8);
	DBG_INFO("Setting serial access mode to 1.. NFC_REG_TIMING_CTL 0x%x\n",
		 ctl);
	writel(ctl, NFC_REG_TIMING_CTL);

	//first_test_nfc(mtd);

	/* FIXME Shouldnt this be with others ecc. defines around other place ? */
	nand->ecc.mode = NAND_ECC_HW;
	nand->ecc.strength = 1;
	nand->ecc.hwctl = nfc_ecc_hwctl;
	nand->ecc.calculate = nfc_ecc_calculate;
	nand->ecc.correct = nfc_ecc_correct;
	nand->select_chip = nfc_select_chip;
	nand->dev_ready = nfc_dev_ready;
	nand->cmdfunc = nfc_cmdfunc;
	nand->read_byte = nfc_read_byte;
	nand->read_buf = nfc_read_buf;
	nand->write_buf = nfc_write_buf;
	nand->waitfunc = nfc_wait;

	/* For various reasons badblock table in flash is not readed,
	 * main reason is that it can be read wrongly, atleast on my flash
	 * BB table doesnt have 4 badblocks at the very end of the flash
	 * You can enable following flags to try it out or completely skip the BBT scan
	 * For now, MTD layer scans entire flash at *every* startup */

	/*nand->options = NAND_SKIP_BBTSCAN;
	   if (use_flash_bbt)
	   nand->bbt_options = NAND_BBT_USE_FLASH; */

	return 0;
}

/*static void print_page(struct mtd_info *mtd, int page)
{
	int i;
	char buff[1024];
	nfc_cmdfunc(mtd, NAND_CMD_READ0, 0, page);
	nfc_read_buf(mtd, buff, 6);
	DBG_INFO("READ: %x %x %x %x %x %x\n",
		 buff[0], buff[1], buff[2], buff[3], buff[4], buff[5]);

	nfc_cmdfunc(mtd, NAND_CMD_READOOB, 0, page);
	nfc_read_buf(mtd, buff, 640);
	for (i = 0; i < 640; i++)
		printk("%02x ", buff[i]);
	printk("\n");
}*/

/*
static void test_nfc(struct mtd_info *mtd)
{
	int i, j, n=0;
	struct nand_chip *nand = mtd->priv;
	int page = 1280;
	unsigned char buff[1024];
	int blocks = 2, num_blocks = mtd->writesize / 1024;

	DBG_INFO("============== TEST NFC ================\n");

	// read page
	print_page(mtd, page);

	// erase block
	nfc_cmdfunc(mtd, NAND_CMD_ERASE1, 0, page);
	nfc_cmdfunc(mtd, NAND_CMD_ERASE2, -1, -1);
	nfc_wait(mtd, nand);
	print_page(mtd, page);

	// write block
	nfc_cmdfunc(mtd, NAND_CMD_SEQIN, 0, page);mtd->
	for (i = 0; i < blocks; i++) {
		for (j = 0; j < 1024; j++, n++)
			buff[j] = n % 256;
		nfc_write_buf(mtd, buff, 1024);
	}
	for ( ; i < num_blocks; i++) {
		memset(buff, 0xff, 1024);
		nfc_write_buf(mtd, buff, 1024);
	}
	// wrong mtd->oobsize for SAMSUNG K9GBG08U0A
	for (i = 0, n = 128; i < 640; i++, n++)
		buff[i] = n % 256;
	nfc_write_buf(mtd, buff, 1024);
	nfc_cmdfunc(mtd, NAND_CMD_PAGEPROG, -1, -1);
	nfc_wait(mtd, nand);
	print_page(mtd, page);

	// test oob write
	nfc_cmdfunc(mtd, NAND_CMD_SEQIN, mtd->writesize, page);
	for (i = 0, n = 0xff; i < 640; i++, n++)
		buff[i] = n % 256;
	nfc_write_buf(mtd, buff, 1024);
	nfc_cmdfunc(mtd, NAND_CMD_PAGEPROG, -1, -1);
	nfc_wait(mtd, nand);
	print_page(mtd, page);

}
*/

/*
// Test unit ops
static void test_ops(struct mtd_info *mtd)
{
	uint32_t page = 1280;
	uint32_t v1, v2;

	// test sequence read
	wait_cmdfifo_free();
	// NFC_DATA_TRANS = 1, NFC fetch data to RAM0
	// NFC_CMD_TYPE = 1,2,3 won't read out any thing
	v1 = NAND_CMD_READ0 | NFC_SEQ | NFC_SEND_CMD1 | NFC_DATA_TRANS | NFC_SEND_ADR | NFC_SEND_CMD2 | ((5 - 1) << 16) | NFC_WAIT_FLAG | (3 << 30);
	v2 = NAND_CMD_READSTART;
	writel(page << 16, NFC_REG_ADDR_LOW);
	writel(page >> 16, NFC_REG_ADDR_HIGH);
	//writel(2, NFC_REG_SECTOR_NUM);
	// NFC_REG_CNT = n, fetch n byte to RAM
	writel(1, NFC_REG_CNT);
	writel(v2, NFC_REG_RCMD_SET);
	writel(v1, NFC_REG_CMD);
	wait_cmdfifo_free();
	wait_cmd_finish();
	DBG_INFO("SEQ READ IO: %x %x %x %x %x %x\n", 
			 readb(NFC_REG_IO_DATA), 
			 readb(NFC_REG_IO_DATA), 
			 readb(NFC_REG_IO_DATA), 
			 readb(NFC_REG_IO_DATA), 
			 readb(NFC_REG_IO_DATA), 
			 readb(NFC_REG_IO_DATA));
	DBG_INFO("SEQ READ RAM: %x %x %x %x %x %x\n",
			 readb(NFC_RAM0_BASE),
			 readb(NFC_RAM0_BASE + 1),
			 readb(NFC_RAM0_BASE + 2),
			 readb(NFC_RAM0_BASE + 3),
			 readb(NFC_RAM0_BASE + 4),
			 readb(NFC_RAM0_BASE + 5));
}*/

int nfc_second_init(struct mtd_info *mtd)
{
	int i, err, j;
	uint32_t ctl;
	uint8_t id[8];
	struct nand_chip_param *nand_chip_param, *chip_param = NULL;
	struct nand_chip *nand = mtd->priv;

	// get nand chip id
	nfc_select_chip(mtd, 0);
	nfc_cmdfunc(mtd, NAND_CMD_READID, 0x00, -1);

	for (i = 0; i < 8; i++)
		id[i] = nfc_read_byte(mtd);

	DBG_INFO("nand chip id: %x %x %x %x %x %x %x %x\n",
		 id[0], id[1], id[2], id[3], id[4], id[5], id[6], id[7]);

	// find chip
	nand_chip_param = sunxi_get_nand_chip_param(id[0]);
	for (i = 0; nand_chip_param[i].id_len; i++) {
		int find = 1;
		for (j = 0; j < nand_chip_param[i].id_len; j++) {
			if (id[j] != nand_chip_param[i].id[j]) {
				find = 0;
				break;
			}
		}
		if (find) {
			chip_param = &nand_chip_param[i];
			DBG_INFO("find nand chip in sunxi database\n");
			break;
		}
	}

	// not find
	if (chip_param == NULL) {
		ERR_INFO("can't find nand chip in sunxi database\n");
		return -ENODEV;
	}
	// set final NFC clock freq
	//if (chip_param->clock_freq > 30)
	//      chip_param->clock_freq = 30;
	sunxi_set_nand_clock(chip_param->clock_freq);
	DBG_INFO("set final clock freq to %dMHz\n", chip_param->clock_freq);

	// disable interrupt
	writel(0, NFC_REG_INT);
	// clear interrupt
	writel(readl(NFC_REG_ST), NFC_REG_ST);

	// set ECC mode
	set_ecc_mode(chip_param->ecc_mode);

	// enable NFC
	ctl = NFC_EN;

	/* Bus width
	   if (nand->options & NAND_BUSWIDTH_16) {
	   DBG_INFO("flash chip bus width 16\n");
	   ctl |= (1 & 0x1) << 2;
	   }
	   else {
	   DBG_INFO("flash chip bus width 8\n");
	   } */

	// Page size
	if (nand->page_shift > 14 || nand->page_shift < 10) {
		ERR_INFO("Flash chip page shift out of range %d\n",
			 nand->page_shift);
		err = -EINVAL;
		goto out;
	}
	// 0 for 1K
	ctl |= ((nand->page_shift - 10) & 0xf) << 8;
	writel(ctl, NFC_REG_CTL);

	writel(0xff, NFC_REG_TIMING_CFG);
	writel(1 << nand->page_shift, NFC_REG_SPARE_AREA);

	// FIXME why random is disabled? why it doesnt work at all if enabled?
	disable_random();

	// setup ECC layout FIXME
	sunxi_ecclayout.eccbytes = 0;
	sunxi_ecclayout.oobavail = mtd->writesize / 1024 * 4 - 2;
	sunxi_ecclayout.oobfree->offset = 1;
	sunxi_ecclayout.oobfree->length = mtd->writesize / 1024 * 4 - 2;
	nand->ecc.layout = &sunxi_ecclayout;
	nand->ecc.size = mtd->writesize;
	nand->ecc.steps = 8;
	nand->ecc.bytes = 0;

	// setup DMA
	dma_hdle = dma_nand_request(1);
	if (dma_hdle == 0) {
		ERR_INFO("request DMA fail\n");
		err = -ENODEV;
		goto out;
	}
	// alloc buffer
	buffer_size = mtd->writesize + 448;
	read_buffer = kmalloc(buffer_size, GFP_KERNEL);
	if (read_buffer == NULL) {
		ERR_INFO("alloc read buffer fail\n");
		err = -ENOMEM;
		goto release_dma_out;
	}
	write_buffer = kmalloc(buffer_size, GFP_KERNEL);
	if (write_buffer == NULL) {
		ERR_INFO("alloc write buffer fail\n");
		err = -ENOMEM;
		goto free_read_out;
	}
	// map 
	read_buffer_dma =
	    dma_map_single(NULL, read_buffer, buffer_size, DMA_FROM_DEVICE);
	write_buffer_dma =
	    dma_map_single(NULL, write_buffer, buffer_size, DMA_TO_DEVICE);

	DBG_INFO
	    ("OOB size = %d  page size = %d  block size = %d  total size = %lld\n",
	     mtd->oobsize, mtd->writesize, mtd->erasesize, mtd->size);

	// register IRQ
	if ((err =
	     request_irq(SW_INT_IRQNO_NAND, nfc_interrupt_handler,
			 IRQF_DISABLED, "NFC", mtd)) < 0) {
		ERR_INFO("request IRQ fail\n");
		goto free_write_out;
	}
	// test command
	//test_nfc(mtd);
	//test_ops(mtd);
	//print_page(mtd, 0);

	return 0;

free_write_out:
	kfree(write_buffer);
free_read_out:
	kfree(read_buffer);
release_dma_out:
	dma_nand_release(dma_hdle);
out:
	return err;
}

void nfc_exit(struct mtd_info *mtd)
{
	//free_irq(SW_INT_IRQNO_NAND, mtd);
	//dma_unmap_single(NULL, read_buffer_dma, buffer_size, DMA_FROM_DEVICE);
	//dma_unmap_single(NULL, write_buffer_dma, buffer_size, DMA_TO_DEVICE);
	//dma_nand_release(dma_hdle);
	kfree(write_buffer);
	kfree(read_buffer);
	sunxi_release_nand_pio();
	release_nand_clock();
}
