module automatic tb_program (
    input logic         Clk,
    output logic        Rst_n,
    output logic        RXD,
    input logic         TXD,
    input logic [7:0]   Temp,
    input logic [7:0]   Switches,
    output logic [11:0] ROM_Data,
    input logic [11:0]  ROM_Addr
    );

    timeprecision 1ps;
    timeunit      1ns;

    localparam logic [31:0] FREQ_CLK = 100000000;
    localparam logic [31:0] TX_SPEED = 115200;
    localparam integer BIT_CYCLES = FREQ_CLK / TX_SPEED;

    // ROM Model
    logic [11:0] ROM [4096];
    assign ROM_Data = ROM[ROM_Addr];

    task init_rom ();
        $display("@%0d: Initializing ROM", $time);
        // Sum 2 and 3
        ROM['h0] = {TYPE_3, LD_SRC_CONSTANT, DST_A}; // LD #2 Ra
        ROM['h1] = 8'h2;
        ROM['h2] = {TYPE_3, LD_SRC_CONSTANT, DST_B}; // LD #3 Rb
        ROM['h3] = 8'h3;
        ROM['h4] = {TYPE_1, ALU_ADD};
        // And store result in memory addres 0x40
        ROM['h5] = {TYPE_3, WR_SRC_ACC, DST_MEM}; // MV Acc #40
        ROM['h6] = 8'h40;
        // Readback from address 0x40
        ROM['h7] = {TYPE_3, LD_SRC_MEM, DST_A}; // LD  0x40 Ra
        ROM['h8] = 8'h40;
        // Shift operations (acc)
        ROM['h9] = {TYPE_1, ALU_SHIFTL}; // SHL
        ROM['hA] = {TYPE_1, ALU_SHIFTR}; // SHR
        // Jump to address 0x30
        ROM['hB] = {TYPE_1, ALU_ASCII2BIN};
        ROM['hC] = {TYPE_1, ALU_BIN2ASCII};
        ROM['hD] = {TYPE_1, ALU_AND};
        ROM['hE] = {TYPE_2, JMP_UNCOND};
        ROM['hF] = 8'h20;
        // DMA TX
        ROM['h20] = {TYPE_3, LD_SRC_CONSTANT, DST_ACC}; // Load DMA TX registers:
        ROM['h21] = 'hAB;                               // Requires write to acc and
        ROM['h22] = {TYPE_3, WR_SRC_ACC, DST_MEM};      // from acc to mem.
        ROM['h23] = DMA_TX_BUFFER_MSB;                  // One for MSB and other
        ROM['h24] = {TYPE_3, LD_SRC_CONSTANT, DST_ACC}; // for LSB
        ROM['h25] = 'hCD;
        ROM['h26] = {TYPE_3, WR_SRC_ACC, DST_MEM};
        ROM['h27] = DMA_TX_BUFFER_LSB;
        // TX Enable
        ROM['h28] = {TYPE_4, 6'h0};
        // Infinite loop
        ROM['h29] = {TYPE_2, JMP_UNCOND};
        ROM['h2A] = 8'h20;
    endtask: init_rom

    task reset_system;
        init_values;
        repeat (10) @(posedge Clk);
        Rst_n<= 0;
        repeat (10) @(posedge Clk);
        Rst_n  <= 1;
        repeat (10) @(posedge Clk);
    endtask : reset_system

    // RX DMA - UART to Memory
    task serial_rx (input logic [7:0] Data);
        @(posedge Clk);
        // Start bit
        RXD    = 1'b0;
        repeat (BIT_CYCLES) @(posedge Clk);
        // Data bits
        for (int i=0; i<8; ++i) begin
            RXD = Data[i];
            repeat (BIT_CYCLES) @(posedge Clk);
        end
        // Stop bit
        RXD= 1'b1;
        repeat (BIT_CYCLES) @(posedge Clk);
        // Wrapup
        $display("@%0d: End of Serial RX", $time);
        @(posedge Clk); // Resync
    endtask: serial_rx

endmodule: tb_program



class axi_ax_beat #(
    parameter AW = 32,
    parameter IW = 8 ,
    parameter UW = 1
);
    rand logic [IW-1:0] ax_id     = '0;
    rand logic [AW-1:0] ax_addr   = '0;
    logic [7:0]         ax_len = '0;
    logic [2:0]         ax_size = '0;
    logic [1:0]         ax_burst = '0;
    logic               ax_lock   = '0;
    logic [3:0]         ax_cache  = '0;
    logic [2:0]         ax_prot   = '0;
    rand logic [3:0]    ax_qos    = '0;
    logic [3:0]         ax_region = '0;
    logic [5:0]         ax_atop   = '0; // Only defined on the AW channel.
    rand logic [UW-1:0] ax_user   = '0;

    task send_w (
        input logic [DW-1:0] data,
        input logic [DW/8-1:0] strb
    );
        axi.w_data <= #TA data;
        axi.w_strb <= #TA strb;
        axi.w_valid <= #TA 1;
        cycle_start();
        while (axi.w_ready != 1) begin cycle_end(); cycle_start(); end
        cycle_end();
        axi.w_data <= #TA '0;
        axi.w_strb <= #TA '0;
        axi.w_valid <= #TA 0;
    endtask

endclass
