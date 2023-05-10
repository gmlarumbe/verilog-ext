interface <uvm_name>_monitor_bfm # (
    // ...
) (
    input logic clk,
    input logic resetn,
    // ...
);

    `include "uvm_macros.svh"
    import uvm_pkg::*;
    import <uvm_name>_agent_pkg::*;

    // Members
    <uvm_name>_monitor proxy;

    // Methods
    task run();
        <uvm_name>_seq_item item;
        <uvm_name>_seq_item cloned_item;

        forever begin
            // ...
            wait(...);
            item = <uvm_name>_seq_item::type_id::create("item");

            // Clone and publish the cloned item to the subscribers
            $cast(cloned_item, item.clone());
            proxy.notify_transaction(cloned_item);
        end
    endtask : run

endinterface : <uvm_name>_monitor_bfm
