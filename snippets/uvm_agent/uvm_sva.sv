interface <uvm_name>_sva # (
    // ...
) (
    input logic aclk,
    input logic aresetn,

    // ...
);

    `include "uvm_macros.svh"
    import uvm_pkg::*;

    // Default clocking and disable iff
    default clocking cb @(posedge aclk);
    endclocking: cb

    default disable iff !aresetn;

    ///////////////////////////////////////////
    // Example: AXI-Lite protocol assertions //
    ///////////////////////////////////////////
    // Parameters
    localparam int MAX_WAIT = 20;

    // Properties
    property p_wvalid;
        wvalid |-> ##[0:MAX_WAIT-1] wready;
    endproperty

    // Assertions
    AP_WVALID : assert property (p_wvalid)
        `uvm_info("AXI_LITE_SVA_AP_WVALID", $sformatf("wvalid channel request acknowledged"), UVM_HIGH)
    else
        `uvm_error("AXI_LITE_SVA_AP_WVALID", $sformatf("wvalid channel request timeout!"))


endinterface: <uvm_name>_sva
