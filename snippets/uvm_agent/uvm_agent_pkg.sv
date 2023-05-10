package <uvm_name>_agent_pkg;

    import uvm_pkg::*;
    `include "uvm_macros.svh"

    `include "<uvm_name>_types.svh"
    `include "<uvm_name>_seq_item.svh"
    `include "<uvm_name>_agent_config.svh"
    `include "<uvm_name>_driver.svh"
    `include "<uvm_name>_monitor.svh"
    typedef uvm_sequencer#(<uvm_name>_seq_item) <uvm_name>_sequencer;
    `include "<uvm_name>_agent.svh"

    // Utility Sequences
    `include "<uvm_name>_seq_lib.svh"

endpackage : <uvm_name>_agent_pkg
