module counter_assert (
input clk,
input rst,
input up,
input [3:0] dout
);
  
  
  /* (1) Behavior of the dout when rst asserted */
  
    ////dout is zero in next clock tick after rst
  
   DOUT_RST_ASRT_1: assert property (@(posedge clk) $rose(rst) |=> (dout == 0));
  
    ///// dout is zero for all clock ticks during rst
    DOUT_RST_ASRT_2: assert property (@(posedge clk) rst |-> (dout == 0));
  
    ////// dout remain stable to zero for entire duration of rst
    
    DOUT_RST_ASRT_3: assert property (@(posedge clk) $rose(rst) |=> rst throughout ((dout == 0)[*1:36]));
 
  
    
    
     
    /* (2) dout is unknown anywhere in the simulation */
    
     //////dout must be valid after rst deassert
    
   DOUT_UNKNW_1: assert property(@(posedge clk) $fell(rst) |-> !$isunknown(dout));
    
     ////// dout must be valid for all clock edges
 
   always@(posedge clk)
    begin
     DOUT_UNKNW_2: assert(!$isunknown(dout));
    end
 
  
     
     
     
     
     
     
     
  
     /* (3)   verifying up and down state of the counter  */
  
     
//////current value of dout must be one greater than previous value when up = 1
     
UP_MODE_1: assert property (@(posedge clk) disable iff(rst) up |-> (dout == $past(dout + 1)) || (dout == 0));
  
/////// next value must be greater than zero when up = 1 and rst = 0 
  
UP_MODE_2: assert property (@(posedge clk) $fell(rst) |=> (dout != 0));   
UP_MODE_3: assert property(@(posedge clk) $fell(rst) |-> up[->1] ##1 !$stable(dout));
 
  
  
//////current value of dout must be one less than previous value when up = 0
  
DOWN_MODE_1: assert property (@(posedge clk) disable iff(rst) !up |-> (dout == $past(dout - 1)) || (dout == 0) || ($past(dout) == 0));
  
 
/////// next value must not be equal to zero when up = 0 and rst = 0   
  DOWN_MODE_2: assert property(@(posedge clk) (!up && !rst) |=> !$stable(dout));   
 
  ///////alternate way 
  
  
 property p1;
   if(up)
     ((dout == $past(dout + 1)) || (dout == 0))
     else
       ((dout == $past(dout - 1)) || (dout == 0) || ($past(dout) == 0)); 
 endproperty
 
  
  
  BOTH_MODE_1:assert property(@(posedge clk) !rst |-> p1);
 
 
 
  
   endmodule
 
 
 
 
 
 
 
 
 
 
 
 
 
/////////////////////////////////////////////////
module tb;
  reg clk = 0,rst = 0,up = 0;
 wire [3:0] dout;
  reg temp = 0;
  
  initial begin
    #342;
    temp = 1;
    #10;
    temp = 0;
  end
  
  counter dut (clk,rst,up,dout);  
  
  bind counter counter_assert dut2 (clk,rst,up,dout);
  
  
  always #5 clk = ~clk;
  
  initial begin
    rst = 1;
    #30;
    rst = 0;
    up = 1;
    #200;
    up = 0;
    rst = 1;
    #25;
    rst = 0;
    
  end
  
  initial begin
    $dumpfile("dump.vcd");
    $dumpvars;
    $assertvacuousoff(0);
    #360;
    $finish;
  end
 
 
endmodule