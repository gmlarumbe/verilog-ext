class <uvm_name>_agent_config extends uvm_object;
    `uvm_object_utils(<uvm_name>_agent_config)

    // BFM Virtual Interfaces
    virtual <uvm_name>_monitor_bfm mon_bfm;
    virtual <uvm_name>_driver_bfm  drv_bfm;

    // Data Members
    uvm_active_passive_enum active = UVM_ACTIVE;

    // Methods
    extern function new(string name = "<uvm_name>_agent_config");
    extern static function <uvm_name>_agent_config get_config(uvm_component c);

endclass : <uvm_name>_agent_config


// ------------------------------
// External method definitions
// ------------------------------
function <uvm_name>_agent_config::new(string name = "<uvm_name>_agent_config");
    super.new(name);
endfunction


function <uvm_name>_agent_config <uvm_name>_agent_config::get_config(uvm_component c);
    <uvm_name>_agent_config t;

    if (!uvm_config_db #(<uvm_name>_agent_config)::get(c, "", "<uvm_name>_agent_config", t)) begin
        `uvm_fatal("CONFIG_LOAD", $sformatf("Cannot get() configuration <uvm_name>_agent_config from uvm_config_db."))
    end

    return t;
endfunction
