onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate -radix hexadecimal /tb_top/clk
add wave -noupdate -radix hexadecimal /tb_top/rst
add wave -noupdate -radix hexadecimal /tb_top/done
add wave -noupdate -radix hexadecimal /tb_top/vector
add wave -noupdate -radix hexadecimal /tb_top/result
add wave -noupdate -radix hexadecimal /tb_top/correct_mix_out
add wave -noupdate -radix hexadecimal /tb_top/is_mistake
add wave -noupdate -radix hexadecimal /tb_top/passed
add wave -noupdate -radix hexadecimal /tb_top/failed
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {0 ps} 0}
quietly wave cursor active 0
configure wave -namecolwidth 150
configure wave -valuecolwidth 100
configure wave -justifyvalue left
configure wave -signalnamewidth 0
configure wave -snapdistance 10
configure wave -datasetprefix 0
configure wave -rowmargin 4
configure wave -childrowmargin 2
configure wave -gridoffset 0
configure wave -gridperiod 1
configure wave -griddelta 40
configure wave -timeline 0
configure wave -timelineunits ps
update
WaveRestoreZoom {0 ps} {1 ns}
