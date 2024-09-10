#s(hash-table test equal data
	      (("tb_program" :file "../files/common/tb_program.sv" :line 23)
	       (:type "module" :desc "module automatic tb_program (" :col 27)
	       ("Clk" :file "../files/common/tb_program.sv" :line 24)
	       (:type "input logic" :desc "    input logic         Clk," :col 24 :parent "tb_program")
	       ("Rst_n" :file "../files/common/tb_program.sv" :line 25)
	       (:type "output logic" :desc "    output logic        Rst_n," :col 24 :parent "tb_program")
	       ("RXD" :file "../files/common/tb_program.sv" :line 26)
	       (:type "output logic" :desc "    output logic        RXD," :col 24 :parent "tb_program")
	       ("TXD" :file "../files/common/tb_program.sv" :line 27)
	       (:type "input logic" :desc "    input logic         TXD," :col 24 :parent "tb_program")
	       ("Temp" :file "../files/common/tb_program.sv" :line 28)
	       (:type "input logic [7:0]" :desc "    input logic [7:0]   Temp," :col 24 :parent "tb_program")
	       ("Switches" :file "../files/common/tb_program.sv" :line 29)
	       (:type "input logic [7:0]" :desc "    input logic [7:0]   Switches," :col 24 :parent "tb_program")
	       ("ROM_Data" :file "../files/common/tb_program.sv" :line 30)
	       (:type "output logic [11:0]" :desc "    output logic [11:0] ROM_Data," :col 24 :parent "tb_program")
	       ("ROM_Addr" :file "../files/common/tb_program.sv" :line 31)
	       (:type "input logic [11:0]" :desc "    input logic [11:0]  ROM_Addr" :col 24 :parent "tb_program")
	       ("FREQ_CLK" :file "../files/common/tb_program.sv" :line 37)
	       (:type "localparam logic [31:0]" :desc "    localparam logic [31:0] FREQ_CLK = 100000000;" :col 28 :parent "tb_program")
	       ("TX_SPEED" :file "../files/common/tb_program.sv" :line 38)
	       (:type "localparam logic [31:0]" :desc "    localparam logic [31:0] TX_SPEED = 115200;" :col 28 :parent "tb_program")
	       ("BIT_CYCLES" :file "../files/common/tb_program.sv" :line 39)
	       (:type "localparam integer" :desc "    localparam integer BIT_CYCLES = FREQ_CLK / TX_SPEED;" :col 23 :parent "tb_program")
	       ("ROM" :file "../files/common/tb_program.sv" :line 55)
	       (:type "logic [11:0]" :desc "    logic [11:0] ROM [4096];" :col 17 :parent "tb_program")
	       ("Data" :file "../files/common/tb_program.sv" :line 115)
	       (:type "input logic [7:0]" :desc "    task serial_rx (input logic [7:0] Data);" :col 38 :parent "tb_program")
	       ("i" :file "../files/common/tb_program.sv" :line 121)
	       (:type "int" :desc "        for (int i=0; i<8; ++i) begin" :col 17 :parent "tb_program")
	       ("init_rom" :file "../files/common/tb_program.sv" :line 58)
	       (:type "task" :desc "    task init_rom ();" :col 9 :parent "tb_program")
	       ("init_values" :file "../files/common/tb_program.sv" :line 99)
	       (:type "task" :desc "    task init_values;" :col 9 :parent "tb_program")
	       ("reset_system" :file "../files/common/tb_program.sv" :line 104)
	       (:type "task" :desc "    task reset_system;" :col 9 :parent "tb_program")
	       ("serial_rx" :file "../files/common/tb_program.sv" :line 115)
	       (:type "task" :desc "    task serial_rx (input logic [7:0] Data);" :col 9 :parent "tb_program")))