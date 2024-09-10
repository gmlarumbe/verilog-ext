module tb_uart () ;

    // Simulation parameters
    timeprecision 1ps;
    timeunit      1ns;
    localparam CLKT = 10ns;  // 100 MHz

    localparam [31:0] FREQ_CLK = 100000000;
    localparam [31:0] TX_SPEED = 115200;
    localparam integer BIT_CYCLES = FREQ_CLK / TX_SPEED;

    // Non-auto signals
    logic Clk             = 1'b0;
    logic Rst_n           = 1'b1;

    logic Data_Read       = 1'b0;
    logic RXD             = 1'b1;
    logic [7:0] TX_DataIn = 1'b0;
    logic TX_Valid        = 1'b0;

    logic [7:0] Data_Out;
    logic Empty;
    logic Full;
    logic TXD;
    logic TX_Ready;


    // System Clock
    always begin
        #(CLKT/2) Clk = ~Clk;
    end

    // DUT Instantiation
    uart # (
        .FREQ_CLK (FREQ_CLK),
        .TX_SPEED (TX_SPEED)
        ) DUT (
        .Clk       (Clk),
        .Rst_n     (Rst_n),
        .TX_Ready  (TX_Ready),
        .TX_Valid  (TX_Valid),
        .TX_DataIn (TX_DataIn),
        .TXD       (TXD),
        .RXD       (RXD),
        .Data_Out  (Data_Out),
        .Data_Read (Data_Read),
        .Full      (Full),
        .Empty     (Empty)
        );


    // Tasks
    task reset_system;
        repeat (10) @(posedge Clk);
        Rst_n = 0;
        repeat (10) @(posedge Clk);
        Rst_n = 1;
        repeat (10) @(posedge Clk);
    endtask : reset_system


    task serial_rx (input logic [7:0] Data);
        @(posedge Clk);
        // Start bit
        RXD = 1'b0;
        repeat (BIT_CYCLES) @(posedge Clk);
        // Data bits
        for (int i=0; i<8; ++i) begin
            RXD = Data[i];
            repeat (BIT_CYCLES) @(posedge Clk);
        end
        // Stop bit
        RXD = 1'b1;
        repeat (BIT_CYCLES) @(posedge Clk);
        // Wrapup
        $display("@%0d: End of Serial RX", $time);
        @(posedge Clk); // Resync
    endtask: serial_rx


    task serial_tx (input logic [7:0] Data);
        TX_DataIn <= Data;
        TX_Valid <= 1'b1;
        @(posedge Clk);
        TX_Valid <= 1'b0;
        @(posedge TX_Ready);
        $display("@%0d: End of Serial TX", $time);
        @(posedge Clk); // Resync
    endtask: serial_tx



    task read_from_fifo ();
        repeat (3) begin
            Data_Read <= 1'b1;
            @(posedge Clk);
            Data_Read <= 1'b0;
            @(posedge Clk);
        end
    endtask: read_from_fifo



    // === TB Setup === \\
    //$timeformat params:
    //1) Scaling factor (–9 for nanoseconds, –12 for picoseconds)
    //2) Number of digits to the right of the decimal point
    //3) A string to print after the time value
    //4) Minimum field width
    initial begin
        $dumpfile("tb_uart.lx2");  // iverilog, vpp & gtkwave
        $dumpvars(0, tb_uart);     // Module Output file
        $timeformat(-9, 3, "ns", 8);
    end


    // Stimuli
    initial begin
        reset_system;

        repeat (3000) @(posedge Clk);
        serial_tx('hAA);
        repeat (3000) @(posedge Clk);
        serial_tx('h03);
        repeat (3000) @(posedge Clk);
        serial_tx('hCC);
        repeat (3000) @(posedge Clk);

        serial_rx('hAA);
        repeat (3000) @(posedge Clk);
        serial_rx('h03);
        repeat (3000) @(posedge Clk);
        serial_rx('hCC);
        repeat (3000) @(posedge Clk);

        read_from_fifo;
        repeat (3000) @(posedge Clk);

        $display("@%0d: TEST PASSED", $time);
        $finish;
    end


endmodule // tb_uart
