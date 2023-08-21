// test/files/common/axi_test.sv:1198
// text_macro_usage not supported inside tasks/functions/procedural blocks

task foo;

`ifdef XSIM
          // std::randomize(w_beat) may behave differently to w_beat.randomize() wrt. limited ranges
          // Keeping alternate implementation for XSIM only
          rand_success = std::randomize(w_beat); assert (rand_success);
`else
          rand_success = w_beat.randomize(); assert (rand_success);
`endif

endtask

function foo;

`ifdef XSIM
          // std::randomize(w_beat) may behave differently to w_beat.randomize() wrt. limited ranges
          // Keeping alternate implementation for XSIM only
          rand_success = std::randomize(w_beat); assert (rand_success);
`else
          rand_success = w_beat.randomize(); assert (rand_success);
`endif

endfunction

module foo;

initial begin

`ifdef XSIM
          // std::randomize(w_beat) may behave differently to w_beat.randomize() wrt. limited ranges
          // Keeping alternate implementation for XSIM only
          rand_success = std::randomize(w_beat); assert (rand_success);
`else
          rand_success = w_beat.randomize(); assert (rand_success);
`endif

end

endmodule

class foo;

`ifdef XSIM
          // std::randomize(w_beat) may behave differently to w_beat.randomize() wrt. limited ranges
          // Keeping alternate implementation for XSIM only
          rand_success = std::randomize(w_beat); assert (rand_success);
`else
          rand_success = w_beat.randomize(); assert (rand_success);
`endif

endclass

package foo;

`ifdef XSIM
          // std::randomize(w_beat) may behave differently to w_beat.randomize() wrt. limited ranges
          // Keeping alternate implementation for XSIM only
          rand_success = std::randomize(w_beat); assert (rand_success);
`else
          rand_success = w_beat.randomize(); assert (rand_success);
`endif

endpackage

module foo;

`ifdef XSIM
          // std::randomize(w_beat) may behave differently to w_beat.randomize() wrt. limited ranges
          // Keeping alternate implementation for XSIM only
          rand_success = std::randomize(w_beat); assert (rand_success);
`else
          rand_success = w_beat.randomize(); assert (rand_success);
`endif

endmodule
