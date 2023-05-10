class <uvm_name>_seq_item extends uvm_sequence_item;
    `uvm_object_utils(<uvm_name>_seq_item)

    // Data Members
    logic [31:0] data;

    // Methods
    extern function new(string name = "<uvm_name>_seq_item");
    extern function void do_copy(uvm_object rhs);
    extern function bit do_compare(uvm_object rhs, uvm_comparer comparer);
    extern function string convert2string();
    extern function void do_print(uvm_printer printer);
    extern function void do_record(uvm_recorder recorder);
    // ModelSim randomize equivalent
    extern function int my_randomize();

endclass : <uvm_name>_seq_item


// ------------------------------
// External method definitions
// ------------------------------
function <uvm_name>_seq_item::new(string name = "<uvm_name>_seq_item");
    super.new(name);
endfunction


function void <uvm_name>_seq_item::do_copy(uvm_object rhs);
    <uvm_name>_seq_item rhs_;

    if(!$cast(rhs_, rhs)) begin
        `uvm_fatal("do_copy", "cast of rhs object failed")
    end
    super.do_copy(rhs);
    data = rhs_.data;
    // ...

endfunction : do_copy


function bit <uvm_name>_seq_item::do_compare(uvm_object rhs, uvm_comparer comparer);
    <uvm_name>_seq_item rhs_;

    if(!$cast(rhs_, rhs)) begin
        `uvm_error("do_compare", "cast of rhs object failed")
        return 0;
    end
    return super.do_compare(rhs, comparer) &&
           data == rhs_.data;
           // ...

endfunction : do_compare


function string <uvm_name>_seq_item::convert2string();
    string s;

    $sformat(s, "%s----------------------------\n", s);
    $sformat(s, "%s| <uvm_name> transaction:\n", s);
    $sformat(s, "%s----------------------------\n", s);
    $sformat(s, "%s| data   = 0x%0h\n", s, data);
    $sformat(s, "%s----------------------------", s);

    return s;

endfunction : convert2string


function void <uvm_name>_seq_item::do_print(uvm_printer printer);
    printer.m_string = convert2string();
endfunction : do_print


function void <uvm_name>_seq_item::do_record(uvm_recorder recorder);
    super.do_record(recorder);
    `uvm_record_field("data", data)
    // ...
endfunction : do_record


function int <uvm_name>_seq_item::my_randomize ();
    // ...

    return 1; // Always successful

endfunction : my_randomize
