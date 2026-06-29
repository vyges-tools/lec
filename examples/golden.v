// golden: f = a & b
module top(a, b, f);
  input  a, b;
  output f;
  AND2 g1(.A(a), .B(b), .Z(f));
endmodule
