// verilog-ts-mode #3: No indentation for first package import in module declaration
module foo
import bar_pkg::*;
  import baz_pkg::*;
  (
  input wire clk,
  input wire rst
  );

endmodule // foo
