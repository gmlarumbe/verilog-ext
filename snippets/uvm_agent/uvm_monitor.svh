class <uvm_name>_monitor extends uvm_component;
    `uvm_component_utils(<uvm_name>_monitor);

    local virtual <uvm_name>_monitor_bfm m_bfm;
    <uvm_name>_agent_config m_cfg;
    uvm_analysis_port #(<uvm_name>_seq_item) ap;

    // Methods
    extern function new(string name = "<uvm_name>_monitor", uvm_component parent = null);
    extern function void build_phase(uvm_phase phase);
    extern task run_phase(uvm_phase phase);
    extern function void notify_transaction(<uvm_name>_seq_item item);

endclass : <uvm_name>_monitor


// ------------------------------
// External method definitions
// ------------------------------
function <uvm_name>_monitor::new(string name = "<uvm_name>_monitor", uvm_component parent = null);
    super.new(name, parent);
endfunction


function void <uvm_name>_monitor::build_phase(uvm_phase phase);
    if (!uvm_config_db #(<uvm_name>_agent_config)::get(this, "", "<uvm_name>_agent_config", m_cfg)) begin
        `uvm_fatal("CONFIG_LOAD", $sformatf("Cannot get <uvm_name>_agent_config from uvm_config_db."))
    end
    m_bfm = m_cfg.mon_bfm;
    m_bfm.proxy = this;
    ap = new("ap", this);
endfunction : build_phase


task <uvm_name>_monitor::run_phase(uvm_phase phase);
    m_bfm.run();
endtask : run_phase


function void <uvm_name>_monitor::notify_transaction(<uvm_name>_seq_item item);
    ap.write(item);
endfunction : notify_transaction

