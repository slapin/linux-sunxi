#ifndef _SUNXI_NAND_REGS_H
#define _SUNXI_NAND_REGS_H

#define   CCM_IO_BASE                   0xf1c20000
#define   PLL5_CFG_REG                  (CCM_IO_BASE + 0x20)
#define   PLL5_OUT_EXT_DIV_P_SHIFT    16
#define   PLL5_OUT_EXT_DIV_P_MASK     (0x03 << PLL5_OUT_EXT_DIV_P_SHIFT)
#define   PLL5_FACTOR_N_SHIFT         8
#define   PLL5_FACTOR_N_MASK          (0x1f << PLL5_FACTOR_N_SHIFT)
#define   PLL5_FACTOR_K_SHIFT         4
#define   PLL5_FACTOR_K_MASK          (0x03 << PLL5_FACTOR_K_SHIFT)
#define   PLL5_FACTOR_M_SHIFT         0
#define   PLL5_FACTOR_M_MASK          (0x03 << PLL5_FACTOR_M_SHIFT)
#define   AHB_GATING_REG0               (CCM_IO_BASE + 0x60)
#define   AHB_GATING_NAND_CLK_SHIFT   13
#define   NAND_SCLK_CFG_REG             (CCM_IO_BASE + 0x80)
#define   SCLK_GATING_SHIFT           31
#define   CLK_SRC_SEL_SHIFT           24
#define   CLK_SRC_SEL_MASK            (0x03 << CLK_SRC_SEL_SHIFT)
#define   CLK_DIV_RATIO_N_SHIFT       16
#define   CLK_DIV_RATIO_N_MASK        (0x03 << CLK_DIV_RATIO_N_SHIFT)
#define   CLK_DIV_RATIO_M_SHIFT       0
#define   CLK_DIV_RATIO_M_MASK        (0x0f << CLK_DIV_RATIO_M_SHIFT)

#define PIO_IO_BASE                   0xf1c20800
#define PC_CFG0_REG                   (PIO_IO_BASE + 0x48)
#define PC_CFG1_REG                   (PIO_IO_BASE + 0x4c)
#define PC_CFG2_REG                   (PIO_IO_BASE + 0x50)

#define NAND_IO_BASE		0xf1c03000
#define __NFC_REG(x)		(NAND_IO_BASE + x)
/* offset */
#define NFC_REG_o_CTL              0x0000
#define NFC_REG_o_ST               0x0004
#define NFC_REG_o_INT              0x0008
#define NFC_REG_o_TIMING_CTL       0x000C
#define NFC_REG_o_TIMING_CFG       0x0010
#define NFC_REG_o_ADDR_LOW         0x0014
#define NFC_REG_o_ADDR_HIGH        0x0018
#define NFC_REG_o_SECTOR_NUM       0x001C
#define NFC_REG_o_CNT              0x0020
#define NFC_REG_o_CMD              0x0024
#define NFC_REG_o_RCMD_SET         0x0028
#define NFC_REG_o_WCMD_SET         0x002C
#define NFC_REG_o_IO_DATA          0x0030
#define NFC_REG_o_ECC_CTL          0x0034
#define NFC_REG_o_ECC_ST           0x0038
#define NFC_REG_o_DEBUG            0x003C
#define NFC_REG_o_ECC_CNT0         0x0040
#define NFC_REG_o_ECC_CNT1         0x0044
#define NFC_REG_o_ECC_CNT2         0x0048
#define NFC_REG_o_ECC_CNT3         0x004c
#define NFC_REG_o_USER_DATA_BASE   0x0050
#define NFC_REG_o_SPARE_AREA       0x00A0
#define NFC_o_RAM0_BASE            0x0400
#define NFC_o_RAM1_BASE            0x0800
/* registers */
#define NFC_REG_CTL                __NFC_REG( NFC_REG_o_CTL             )
#define NFC_REG_ST                 __NFC_REG( NFC_REG_o_ST              )
#define NFC_REG_INT                __NFC_REG( NFC_REG_o_INT             )
#define NFC_REG_TIMING_CTL         __NFC_REG( NFC_REG_o_TIMING_CTL      )
#define NFC_REG_TIMING_CFG         __NFC_REG( NFC_REG_o_TIMING_CFG      )
#define NFC_REG_ADDR_LOW           __NFC_REG( NFC_REG_o_ADDR_LOW        )
#define NFC_REG_ADDR_HIGH          __NFC_REG( NFC_REG_o_ADDR_HIGH       )
#define NFC_REG_SECTOR_NUM         __NFC_REG( NFC_REG_o_SECTOR_NUM      )
#define NFC_REG_CNT                __NFC_REG( NFC_REG_o_CNT             )
#define NFC_REG_CMD                __NFC_REG( NFC_REG_o_CMD             )
#define NFC_REG_RCMD_SET           __NFC_REG( NFC_REG_o_RCMD_SET        )
#define NFC_REG_WCMD_SET           __NFC_REG( NFC_REG_o_WCMD_SET        )
#define NFC_REG_IO_DATA            __NFC_REG( NFC_REG_o_IO_DATA         )
#define NFC_REG_ECC_CTL            __NFC_REG( NFC_REG_o_ECC_CTL         )
#define NFC_REG_ECC_ST             __NFC_REG( NFC_REG_o_ECC_ST          )
#define NFC_REG_ECC_CNT0           __NFC_REG( NFC_REG_o_ECC_CNT0        )
#define NFC_REG_ECC_CNT1           __NFC_REG( NFC_REG_o_ECC_CNT1        )
#define NFC_REG_ECC_CNT2           __NFC_REG( NFC_REG_o_ECC_CNT2        )
#define NFC_REG_ECC_CNT3           __NFC_REG( NFC_REG_o_ECC_CNT3        )
#define NFC_REG_DEBUG              __NFC_REG( NFC_REG_o_DEBUG           )
#define NFC_REG_USER_DATA(sct_num) __NFC_REG( NFC_REG_o_USER_DATA_BASE + 4 * sct_num )
#define NFC_REG_SPARE_AREA         __NFC_REG( NFC_REG_o_SPARE_AREA      )
#define NFC_RAM0_BASE              __NFC_REG( NFC_o_RAM0_BASE           )
#define NFC_RAM1_BASE              __NFC_REG( NFC_o_RAM1_BASE           )

/*define bit use in NFC_CTL*/
#define NFC_EN			(1 << 0)
#define NFC_RESET		(1 << 1)
#define NFC_BUS_WIDTH		(1 << 2)
#define NFC_RB_SEL		(1 << 3)
#define NFC_CE_SEL		(1 << 24)
#define NFC_CE_CTL		(1 << 6)
#define NFC_CE_CTL1		(1 << 7)
#define NFC_PAGE_SIZE		(0xf << 8)
#define NFC_SAM			(1 << 12)
#define NFC_RAM_METHOD		(1 << 14)
#define NFC_DEBUG_CTL		(1 << 31)

/*define bit use in NFC_ST*/
#define NFC_RB_B2R		(1 << 0)
#define NFC_CMD_INT_FLAG	(1 << 1)
#define NFC_DMA_INT_FLAG	(1 << 2)
#define NFC_CMD_FIFO_STATUS	(1 << 3)
#define NFC_STA			(1 << 4)
#define NFC_NATCH_INT_FLAG	(1 << 5)
#define NFC_RB_STATE0		(1 << 8)
#define NFC_RB_STATE1		(1 << 9)
#define NFC_RB_STATE2		(1 << 10)
#define NFC_RB_STATE3		(1 << 11)

/*define bit use in NFC_INT*/
#define NFC_B2R_INT_ENABLE	(1 << 0)
#define NFC_CMD_INT_ENABLE	(1 << 1)
#define NFC_DMA_INT_ENABLE	(1 << 2)

/*define bit use in NFC_CMD*/
#define NFC_CMD_LOW_BYTE	(0xff << 0)
#define NFC_CMD_HIGH_BYTE	(0xff << 8)
#define NFC_ADR_NUM		(0x7 << 16)
#define NFC_SEND_ADR		(1 << 19)
#define NFC_ACCESS_DIR		(1 << 20)
#define NFC_DATA_TRANS		(1 << 21)
#define NFC_SEND_CMD1		(1 << 22)
#define NFC_WAIT_FLAG		(1 << 23)
#define NFC_SEND_CMD2		(1 << 24)
#define NFC_SEQ			(1 << 25)
#define NFC_DATA_SWAP_METHOD	(1 << 26)
#define NFC_ROW_AUTO_INC	(1 << 27)
#define NFC_SEND_CMD3           (1 << 28)
#define NFC_SEND_CMD4           (1 << 29)
#define NFC_CMD_TYPE		(3 << 30)

/* define bit use in NFC_RCMD_SET*/
#define NFC_READ_CMD		(0xff<< 0)
#define NFC_RANDOM_READ_CMD0 	(0xff << 8)
#define NFC_RANDOM_READ_CMD1 	(0xff << 16)

/*define bit use in NFC_WCMD_SET*/
#define NFC_PROGRAM_CMD		(0xff << 0)
#define NFC_RANDOM_WRITE_CMD	(0xff << 8)
#define NFC_READ_CMD0		(0xff << 16)
#define NFC_READ_CMD1	        (0xff << 24)

/*define bit use in NFC_ECC_CTL*/
#define NFC_ECC_EN		(1 << 0)
#define NFC_ECC_PIPELINE	(1 << 3)
#define NFC_ECC_EXCEPTION       (1 << 4)
#define NFC_ECC_BLOCK_SIZE	(1 << 5)
#define NFC_RANDOM_EN           (1 << 9)
#define NFC_RANDOM_DIRECTION    (1 << 10)
#define NFC_ECC_MODE_SHIFT      12
#define NFC_ECC_MODE		(0xf << NFC_ECC_MODE_SHIFT)
#define NFC_RANDOM_SEED         (0x7fff << 16)

#define NFC_IRQ_MAJOR		13
/*cmd flag bit*/
#define NFC_PAGE_MODE  		0x1
#define NFC_NORMAL_MODE  	0x0

#define NFC_DATA_FETCH 		0x1
#define NFC_NO_DATA_FETCH 	0x0
#define NFC_MAIN_DATA_FETCH 	0x1
#define NFC_SPARE_DATA_FETCH	0X0
#define NFC_WAIT_RB		0x1
#define NFC_NO_WAIT_RB		0x0
#define NFC_IGNORE		0x0

#define NFC_INT_RB		0
#define NFC_INT_CMD		1
#define NFC_INT_DMA		2
#define NFC_INT_BATCH		5

#endif
