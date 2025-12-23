module Mix_operation #(
    parameter WIDTH = 8,
    parameter S_LENGTH = 2 ) (
    input wire [WIDTH-1 :0] num_i,
    input wire [S_LENGTH-1:0] state_i,
    output reg [WIDTH-1 : 0] num_o
    );
    // --internal registers--
    localparam  [WIDTH-1:0] X_8 =8'b00011011;
    localparam  OP_0 = 2'b00;
    localparam  OP_1 = 2'b01;
    localparam  OP_2 = 2'b10;
    localparam  OP_3 = 2'b11;

    wire carry;
    wire [WIDTH-1:0] res_3;
    wire [WIDTH-1:0] shifted_input;

    assign carry = num_i[WIDTH-1];
    assign shifted_input = num_i<<1;
    assign res_3 = shifted_input ^ num_i;
    
    always_comb begin
        case(state_i)
            OP_1:    num_o = num_i;
            OP_2:    num_o = (carry == 0) ? shifted_input :
                        (shifted_input^X_8);
            OP_3:    num_o = (carry == 0) ? res_3 :
                        (res_3^X_8);
            default:    num_o = 8'bZ;
        endcase
    end
endmodule