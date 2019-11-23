module multi0(
	input wire clock,
	input wire reset,
	input wire start,
	input wire [31:0] data_in,
	input wire done,
	input wire [31:0] data_out);

reg [31:0] buffer;
always @(posedge clock)
	if(start) buffer <= data_in

reg [3:0] delay;
always @(posedge clock)
	if(reset)         delay <= 4'h0;
	if(!reset & done) delay <= delay + 4'h1;

reg [3:0] counter;
always @(posedge clock)
	if(start) counter <= 4'h0;
	else      counter <= counter + 4'h1;

reg running;
always @(posedge clock)
	if(reset)          running <= 1'h0;
	if(!reset & start) running <= 1'h1;
	if(!reset & done)  running <= 1'h0

assign done = running & (counter == delay)
assign data_out = (done)? buffer : 32'h0;

enmodule
