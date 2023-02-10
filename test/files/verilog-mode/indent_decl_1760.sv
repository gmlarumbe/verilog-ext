module test (
input logic a,
output logic b
);

for (genvar i=0; i<2; i++) begin : g_slice

submod
#(
.RESET_POL (RESET_POL)
)u_sub_0(
.clk     (clk),
.reset_n (reset_n),
.d       (d[i]),
.q       (q_0[i])
);

submod
#(
.RESET_POL (RESET_POL)
)u_sub_1(
.clk     (clk),
.reset_n (reset_n),
.d       (q_0[i]),
.q       (q[i])
);

end

endmodule


// Local Variables:
// indent-tabs-mode: nil
// End:
