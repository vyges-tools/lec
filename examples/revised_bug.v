// revised (buggy): f = a | b
module top(a, b, f);
  input  a, b;
  output f;
  OR2 g1(.A(a), .B(b), .Z(f));
endmodule
