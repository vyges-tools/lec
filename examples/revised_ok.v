// revised (De Morgan): f = !(!a | !b)  == a & b
module top(a, b, f);
  input  a, b;
  output f;
  wire na, nb, o;
  INV  i1(.A(a),  .Y(na));
  INV  i2(.A(b),  .Y(nb));
  OR2  o1(.A(na), .B(nb), .Z(o));
  INV  i3(.A(o),  .Y(f));
endmodule
