package foo_pkg;

    // Declarations
    class pkg_cls;
        int pkg_member;

        logic pkg_var [5][$];

        function new(string name="asdf", uvm_component parent);
            super.new(name, parent);
        endfunction : new

    endclass: pkg_cls

endpackage : pkg_cls


module foo;

    pkg_cls cls_inst;

    logic       var2 [5][$];
    logic       var3 [5];
    wire [7:0]  var4 [5];
    wire [7:0]  var5 [$] = '{0, 1};
    wire [7:0]  var6 [];
    wire [7:0]  var7 [7];
    logic [7:0] var8 [int];

    typedef enum logic [2:0] {A, B} type_t;
    type_t my_type;
    enum logic [2:0] {A, B} var_e;

    string s;

    // Completions
    cls_inst.
    var2.
    var3.
    var4.
    var5.
    var6.
    var7.
    var8.
    my_type.
    var_e.
    s.

    always begin
        foo_pkg::
        foo_pkg::pkg_cls::
        foo_pkg::pkg_cls::pkg_var.
        pkg_cls::
        $
        `
    end


endmodule : foo
