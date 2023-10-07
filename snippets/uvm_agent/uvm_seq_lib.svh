class <uvm_name>_seq_base extends uvm_sequence #(<uvm_name>_seq_item);
    `uvm_object_utils(<uvm_name>_seq_base)

    // Data members
    logic [31:0] data = 0;

    // Knobs
    bool_t do_randomize = TRUE;

    // Methods
    function new(string name = "<uvm_name>_seq_base");
        super.new(name);
    endfunction

    task body();
        req = <uvm_name>_seq_item::type_id::create("req");
        // UVM sequence_item operation
        start_item(req);
        if (do_randomize == TRUE) begin
            if(!req.my_randomize()) begin
                `uvm_fatal("body", "req randomization failure")
            end
        end
        finish_item(req);
    endtask : body

endclass : <uvm_name>_seq_base


