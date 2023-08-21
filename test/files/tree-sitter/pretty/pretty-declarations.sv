module ucontroller # (
    parameter logic [31:0] FREQ_CLK = 100000000,
    parameter logic [31:0] TX_SPEED = 115200
) (
    input logic Clk,
    input logic Rst_n,
    // Serial interface
    input logic RXD,
    output logic TXD,
    // ROM
    input logic [11:0] ROM_Data,
    output logic [11:0] ROM_Addr,
    // Exteral HW
    output logic [7:0] Temp,
    output logic [7:0] Switches
);
    // Buses arbitrating
    logic DMA_Oen;
    logic DMA_Wen;
    logic DMA_Cs;
    logic CPU_Oen;
    logic CPU_Wen;
    logic CPU_Cs;
    logic [7:0] CPU_Address;
    logic [7:0] DMA_Address;
    logic [7:0] DMA_DataOut;
    logic [7:0] CPU_DataOut;
    logic Dma_Idle;
    // Serial <-> DMA
    logic [7:0] TX_Data;
    logic TX_Ready;
    logic TX_Valid;
    logic Data_Read;
    logic [7:0] RX_Data;
    logic RX_Empty;
    logic RX_Full;
    // DMA/CPU <-> RAM
    logic [7:0] RAM_DataOut;
    logic [7:0] RAM_DataIn;
    // ALU <-> CPU
    logic [7:0] ALU_DataIn;
    logic [7:0] ALU_DataOut;
    alu_op ALU_op;
    logic FlagE;
    logic FlagN;
    logic FlagC;
    logic FlagZ;
    // RAM signals
    logic [7:0] RAM_Address;
    logic RAM_Wen;
    logic RAM_Oen;
    logic RAM_Cs;
    // DMA <-> CPU
    logic Bus_grant;
    logic Bus_req;
    logic Dma_Tx_Ready;
    logic Dma_Tx_Start;

endmodule


class axi_lite_rand_master #(
    // AXI interface parameters
    parameter int unsigned AW = 0,
    parameter int unsigned DW = 0,
    // Stimuli application and test time
    parameter time  TA = 2ns,
    parameter time  TT = 8ns,
    parameter int unsigned MIN_ADDR = 32'h0000_0000,
    parameter int unsigned MAX_ADDR = 32'h1000_0000,
    // Maximum number of open transactions
    parameter int   MAX_READ_TXNS = 1,
    parameter int   MAX_WRITE_TXNS = 1,
    // Upper and lower bounds on wait cycles on Ax, W, and resp (R and B) channels
    parameter int   AX_MIN_WAIT_CYCLES = 0,
    parameter int   AX_MAX_WAIT_CYCLES = 100,
    parameter int   W_MIN_WAIT_CYCLES = 0,
    parameter int   W_MAX_WAIT_CYCLES = 5,
    parameter int   RESP_MIN_WAIT_CYCLES = 0,
    parameter int   RESP_MAX_WAIT_CYCLES = 20
);

endclass
