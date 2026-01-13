module Mix_columns #(
    parameter DIM  = 4,
    parameter WIDTH = 8 
) (   
    input wire  [WIDTH-1:0] mat_i [DIM-1:0][DIM-1:0],
    output wire [WIDTH-1:0] mat_o [DIM-1:0][DIM-1:0]
);

    localparam [1:0] MIX_COL_MAT [DIM-1:0][DIM-1:0] = '{
        '{8'h02, 8'h03, 8'h01, 8'h01}, // Row 0
        '{8'h01, 8'h02, 8'h03, 8'h01}, // Row 1
        '{8'h01, 8'h01, 8'h02, 8'h03}, // Row 2
        '{8'h03, 8'h01, 8'h01, 8'h02}  // Row 3
    };


    genvar i;
    genvar j;
    genvar k;
    generate    
        for(i = 0; i < DIM; i = i + 1) begin : loop_1
            for(j = 0;j < DIM; j = j + 1) begin : loop_2
                wire [WIDTH-1:0] cur_output_vec [DIM-1:0];

                for (k = 0; k < DIM; k = k + 1) begin : loop_3  
                    Mix_operation AES_module (  
                        .state_i (MIX_COL_MAT[i][k]),
                        .num_i   (mat_i[k][j]),
                        .num_o   ((cur_output_vec[k]))
                    );
                    end
                assign mat_o[i][j] = cur_output_vec[0] ^ cur_output_vec[1] ^ cur_output_vec[2] ^ cur_output_vec[3];
            end
        end
    endgenerate
endmodule