//scope test (p.53)
begin
  var x:=0;
  proc p is (x:=x*2);
  proc q is (call p);
  begin
    var x:=5;
    proc p is (x:=x+1);
    call q;
    y:=x
  end
end
