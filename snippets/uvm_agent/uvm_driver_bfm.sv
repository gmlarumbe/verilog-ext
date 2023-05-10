interface <uvm_name>_driver_bfm # (
    // ...
) (
    input logic clk,
    input logic resetn,
    // ...
);

    timeprecision 1ps;
    timeunit      1ns;

    `include "uvm_macros.svh"
    import uvm_pkg::*;
    import <uvm_name>_agent_pkg::*;

    // Methods
    task init_values ();
        // ...
    endtask : init_values


    task drive (<uvm_name>_seq_item req);
        // ...
    endtask : drive


endinterface : <uvm_name>_driver_bfm
