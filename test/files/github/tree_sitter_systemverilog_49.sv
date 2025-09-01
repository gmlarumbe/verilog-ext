module test;
  wire a, b, c, d;
  reg z;
  always @(*) begin
    if (a)
      z = a;
    else if (b)
      z = b;
    else
      if (c)
        z = c;
      else
        z = d;
  end
endmodule
