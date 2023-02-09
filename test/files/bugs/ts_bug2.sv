// verilog-ts-mode indentation bug:
// Snippet from test/files/indent/indent_task.ts.indent.sv:54
//   Indents wrongly due to errors during parsing.
//   Not sure if generate is allowed inside class.
//   Property/sequence/clocking also have parsing errors

class a;
    virtual function void foo();
        foo  = 2;
    endfunction // void
    extern function void bar();
    function fred();
        aaa;
    endfunction // fred

    task foo;
    endtask // endtask

    virtual task foo;
    endtask // endtask

    generate g;
    endgenerate

        covergroup g;
    endgroup // g

        property p;
    endproperty

        sequence s;
    endsequence // s

        clocking c;
    endclocking // c

        function f;
    endfunction //

        virtual function f;
                endfunction //

    protected function f;
    endfunction //

endclass // a
