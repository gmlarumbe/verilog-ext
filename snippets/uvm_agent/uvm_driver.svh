class <uvm_name>_driver extends uvm_driver #(<uvm_name>_seq_item);
    `uvm_component_utils(<uvm_name>_driver)

    // Data Members
    local virtual <uvm_name>_driver_bfm m_bfm;
    <uvm_name>_agent_config m_cfg;

    // Methods
    extern function new(string name = "<uvm_name>_driver", uvm_component parent = null);
    extern function void build_phase(uvm_phase phase);
    extern function void connect_phase(uvm_phase phase);
    extern task run_phase(uvm_phase phase);

endclass : <uvm_name>_driver


// ------------------------------
// External method definitions
// ------------------------------
function <uvm_name>_driver::new(string name = "<uvm_name>_driver", uvm_component parent = null);
    super.new(name, parent);
endfunction


function void <uvm_name>_driver::build_phase(uvm_phase phase);
endfunction : build_phase


function void <uvm_name>_driver::connect_phase(uvm_phase phase);
    m_bfm = m_cfg.drv_bfm;
endfunction: connect_phase


task <uvm_name>_driver::run_phase(uvm_phase phase);
    <uvm_name>_seq_item req;

    m_bfm.init_values();

    forever begin
        seq_item_port.get_next_item(req);
        m_bfm.drive(req);
        seq_item_port.item_done();
    end
endtask : run_phase
