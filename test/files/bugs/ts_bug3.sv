// Tree-sitter syntax error: forever @event
// should be valid syntax
//
// test/files/indent/indent_begin_clapp.ts.indent.sv

module x;

    forever @E
    begin
        end

endmodule
