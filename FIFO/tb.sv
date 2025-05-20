/////////////////////////////////////////////Testbench Code
 
module assert_fifo (input clk, rst, wr, rd, 
                    input [7:0] din,input [7:0] dout,
            input empty, full);
  
  
  // (1) status of full and empty when rst asserted
  
  ////check on edge
  
 RST_1: assert property (@(posedge clk) $rose(rst) |-> (full == 1'b0 && empty == 1'b1))$info("A1 Suc at %0t",$time);
   
  /////check on level
   
 RST_2: assert property (@(posedge clk) rst |-> (full == 1'b0 && empty == 1'b1))$info("A2 Suc at %0t",$time);  
 
  
   //  (2) operation of full and empty flag
     
   FULL_1: assert property (@(posedge clk) disable iff(rst) $rose(full) |=> (FIFO.wptr == 0)[*1:$] ##1 !full)$info("full Suc at %0t",$time); 
   
   FULL_2 : assert property (@(posedge clk) disable iff(rst) (FIFO.cnt == 15) |-> full)$info("full Suc at %0t",$time);
     
       
   EMPTY_1:  assert property (@(posedge clk) disable iff(rst) $rose(empty) |=> (FIFO.rptr == 0)[*1:$] ##1 !empty)$info("full Suc at %0t",$time); 
       
  
  EMPTY_2: assert property (@(posedge clk) disable iff(rst) (FIFO.cnt == 0) |-> empty)$info("empty Suc at %0t",$time); 
     
       
       
   ///////  (3) read while empty
  
    READ_EMPTY: assert property (@(posedge clk) disable iff(rst) empty |-> !rd)$info("Suc at %0t",$time);  
 
      ////////// (4) Write while FULL
     
    WRITE_FULL: assert property (@(posedge clk) disable iff(rst) full |-> !wr)$info("Suc at %0t",$time);
  
      
      ////////////// (5) Write+Read pointer behavior with rd and wr signal
 
      
      //////if wr high and full is low, wptr must incr
       
  WPTR1: assert property (@(posedge clk)  !rst && wr && !full |=> $changed(FIFO.wptr));
         
    //////// if wr is low, wptr must constant
  WPTR2: assert property (@(posedge clk) !rst && !wr |=> $stable(FIFO.wptr));
    
    /////// if rd is high, wptr must stay constant
  WPTR3: assert property (@(posedge clk)  !rst && rd |=> $stable(FIFO.wptr)) ;
         
   
  RPTR1: assert property (@(posedge clk)  !rst && rd && !empty |=> $changed(FIFO.rptr));
         
  RPTR2: assert property (@(posedge clk) !rst && !rd |=> $stable(FIFO.rptr));
    
  RPTR3: assert property (@(posedge clk)  !rst && wr |=> $stable(FIFO.rptr));
 
  
      
    
    //////////  (6) state of all the i/o ports for all clock edge
  
  
  
 
 
  always@(posedge clk)
    begin
      assert (!$isunknown(dout));
      assert (!$isunknown(rst));
      assert (!$isunknown(wr));
      assert (!$isunknown(rd));
      assert (!$isunknown(din));
    end
 
 
 
    //////////////////// (7) Data must match
    
  property p1;
    integer waddr;
    logic [7:0] data;
 
    (wr, waddr = tb.i, data = din) |-> ##[1:30] rd ##0 (waddr == tb.i - 1, $display("din: %0d dout :%0d",data, dout));
  endproperty
  
  assert property (@(posedge clk) disable iff(rst) p1) $info("Suc at %0t",$time);
 
endmodule
 
 
//////////////////////////////////////////////////////////////////////////////////////////////
 
 
 
module tb;
  reg clk = 0, rst = 0, wr = 0, rd = 0;
  reg [7:0] din = 0;
  wire [7:0] dout;
  wire empty, full;
  integer i = 0;
  reg start = 0;
  
  initial begin
    #2;
    start = 1;
    #10;
    start = 0;
  end
  
  
  reg temp = 0;
  initial begin
    #292;
    temp = 1;
    #10;
    temp = 0;
  end
  
  FIFO dut (clk,rst,wr,rd,din,dout,empty,full);
  bind FIFO assert_fifo dut2 (clk,rst,wr,rd,din,dout,empty,full);
  
  
  
  always #5 clk = ~clk;
  
  
    task write();
    for( i = 0; i < 15; i++)
      begin   
        
        din = $urandom();
        wr = 1'b1;
        rd = 1'b0;
        @(posedge clk);
      end
  endtask
  
  
      task read();
    for( i = 0; i < 15; i++)
      begin   
        
        wr = 1'b0;
        rd = 1'b1;
        @(posedge clk);
      end
  endtask
  
  
  initial begin
    @(posedge clk) {rst,wr,rd} = 3'b100;
    @(posedge clk) {rst,wr,rd} = 3'b101;
    @(posedge clk) {rst,wr,rd} = 3'b110;
    @(posedge clk) {rst,wr,rd} = 3'b111;
    @(posedge clk) {rst,wr,rd} = 3'b000; 
    
    write();
    @(posedge clk) {rst,wr,rd} = 3'b010;
    @(posedge clk);
    
    read();
    
  end
  
  
  /*
  initial begin
 
    $display("------------Starting Test-----------------");
    $display("------(1) Behavior of FULL and EMPTY on RST High------");
    @(posedge clk) {rst,wr,rd} = 3'b100;
    @(posedge clk) {rst,wr,rd} = 3'b101;
    @(posedge clk) {rst,wr,rd} = 3'b110;
    @(posedge clk) {rst,wr,rd} = 3'b111;
    @(posedge clk) {rst,wr,rd} = 3'b000;
    @(posedge clk);
    #20;
 
    $display("------(2) Reading from Empty FIFO------");
    @(posedge clk) {rst,wr,rd} = 3'b001;
    @(posedge clk);
    
    #20;
    $display("------(3) Writing Data to FULL FIFO------");
    $display("--------(4) RPTR and WPTR behavior during Writing--------");
    write();
    @(posedge clk) {rst,wr,rd} = 3'b010;
    @(posedge clk);
    
    #20;
    $display("--------(5) RPTR and WPTR behavior during reading--------");
    read();
    
        
    
  end
  */
 
  
  //// ---------------- (6) Data Matched during read and write operation
  /*
  initial begin
    write();
    repeat(5) @(posedge clk);
    read(); 
  end
  
 */ 
     
   
  
  
  initial begin
    $dumpfile("dump.vcd");
    $dumpvars;
    $assertvacuousoff(0);
    #500;
    $finish();
  end
  
endmodule  
 