
module register (
    input wire clk,
    input wire rst,
    input wire [4:0] in,
    output wire [4:0] out
);
    // Takes an input and delays it by 1 cycle.
    reg [4:0] r;
    wire [4:0] next_r = rst ? 0 : in;
    always @(posedge clk) begin
        r <= next_r;
    end
    assign out = r;
endmodule
