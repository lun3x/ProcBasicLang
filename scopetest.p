//scope test (p.53)
y := 1;
x := 8;
z := 2;
begin
  var x := 0;
  proc p is x := x*2;
  begin
    var x := 5;
    y := x;
    proc q = call p
    call q
  end
end
