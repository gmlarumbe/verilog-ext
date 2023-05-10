class <uvm_name>_agent extends uvm_component;
    `uvm_component_utils(<uvm_name>_agent)

    <uvm_name>_monitor   m_monitor;
    <uvm_name>_sequencer m_sequencer;
    <uvm_name>_driver    m_driver;

    <uvm_name>_agent_config m_cfg;
    uvm_analysis_port #(<uvm_name>_seq_item) ap;

    // Methods
    extern function new(string name = "<uvm_name>_agent", uvm_component parent = null);
    extern function void build_phase(uvm_phase phase);
    extern function void connect_phase(uvm_phase phase);

endclass : <uvm_name>_agent


// ------------------------------
// External method definitions
// ------------------------------
function <uvm_name>_agent::new(string name = "<uvm_name>_agent", uvm_component parent = null);
    super.new(name, parent);
endfunction


function void <uvm_name>_agent::build_phase(uvm_phase phase);
    if (!uvm_config_db #(<uvm_name>_agent_config)::get(this, "", "<uvm_name>_agent_config", m_cfg)) begin
        `uvm_fatal("CONFIG_LOAD", $sformatf("Cannot get <uvm_name>_agent_config from uvm_config_db."))
    end
    m_monitor = <uvm_name>_monitor::type_id::create("m_monitor", this);
    m_monitor.m_cfg = m_cfg;

    if(m_cfg.active == UVM_ACTIVE) begin
        m_driver = <uvm_name>_driver::type_id::create("m_driver", this);
        m_driver.m_cfg = m_cfg;
        m_sequencer = <uvm_name>_sequencer::type_id::create("m_sequencer", this);
    end
endfunction : build_phase


function void <uvm_name>_agent::connect_phase(uvm_phase phase);
    ap = m_monitor.ap;

    if(m_cfg.active == UVM_ACTIVE) begin
        m_driver.seq_item_port.connect(m_sequencer.seq_item_export);
    end
endfunction : connect_phase
