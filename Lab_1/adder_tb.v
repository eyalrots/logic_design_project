`timescale 1ns/1ps
module adder_tb;
    reg  [3:0] a, b;
    wire [4:0] sum;
    adder uut (.a(a), .b(b), .sum(sum));

    initial begin
        $display("Starting simulation...");
        a = 0; b = 0;
        #10 a = 3; b = 4;
        #10 a = 7; b = 8;
        #10 a = 15; b = 15;
        //#10 $finish;
    end

    initial begin
        $monitor("Time=%0t | a=%d b=%d sum=%d", $time, a, b, sum);
    end
endmodule