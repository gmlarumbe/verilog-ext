// test/files/indent/indent_double_curly.ts.indent.sv
// Bug in concatenation of always block.
// No support for part_select inside concatenation?
// https://github.com/tree-sitter/tree-sitter-verilog/issues/54

module test;
    always_ff @(posedge clk or negedge rst_n)
        if (~rst_n)
            begin
                a <= {(5){1'b0}};
                a <= 1;
            end

    always_ff @(posedge clk or negedge rst_n)
        if (~rst_n)
            begin
                a <= {5{1'b0}};
                a <= 1;
            end

    always_ff @(posedge clk or negedge rst_n)
        if (~rst_n)
            begin
                a <= {{1'b0,1'b0}};
                a <= 1;
            end

    always_ff @(posedge clk or negedge rst_n)
        if (~rst_n)
            begin
                a <= {b, {1'b0,1'b0}};
                a <= 1;
            end

    always_ff @(posedge clk or negedge rst_n)
        if (~rst_n)
            begin
                a <= {b[1:0], {1'b0,1'b0}};
                a <= 1;
            end
endmodule
