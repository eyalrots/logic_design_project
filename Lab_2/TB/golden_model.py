## in this file we will generate the architecture of mux_colunms to gain knowledge and understanding:
import numpy as np

def binary_matrix_to_hex(bin_matrix: np.ndarray) -> np.ndarray:
    """
    Convert a (rows, cols, 8) binary matrix (0/1, MSB first)
    into a (rows, cols) uint8 matrix of bytes (hex-friendly).
    """
    bin_matrix = np.asarray(bin_matrix, dtype=np.uint8)

    if bin_matrix.ndim != 3 or bin_matrix.shape[2] != 8:
        raise ValueError(f"Expected shape (rows, cols, 8), got {bin_matrix.shape}")

    rows, cols, _ = bin_matrix.shape

    # Flatten to (N, 8), where N = rows * cols
    flat = bin_matrix.reshape(-1, 8)

    # Pack bits into bytes → shape (N, 1)
    packed = np.packbits(flat, axis=1)

    # Reshape back to (rows, cols)
    hex_matrix = packed.reshape(rows, cols)

    return hex_matrix





def hex_matrix_to_binary(hex_matrix: np.ndarray) -> np.ndarray:
    """
    Convert a NumPy matrix of bytes (hex values) with shape (r, c)
    into a binary matrix with shape (r, c, 8), MSB first.
    """
    hex_matrix = np.asarray(hex_matrix, dtype=np.uint8)
    rows, cols = hex_matrix.shape

    # Flatten -> unpack bits -> reshape back
    bin_matrix = np.unpackbits(hex_matrix.reshape(-1, 1), axis=1)
    return bin_matrix.reshape(rows, cols, 8)


def xor_vec(a, b):
    return [ai ^ bi for ai, bi in zip(a, b)]

def shl_with_carry(bits):
    bits = np.asarray(bits, dtype=np.uint8)  # ensure array
    carry = int(bits[0])

    shifted = np.empty_like(bits)
    shifted[:-1] = bits[1:]   # shift left
    shifted[-1] = 0           # new LSB

    return shifted, carry

def speicael_mux(state,vec_i):
    x_8 = [0,0,0,1,1,0,1,1]
    

    if state ==1:
        return vec_i
    elif state == 2:
        cur_output,carry = shl_with_carry(vec_i)
        if carry ==1 :
            return xor_vec(cur_output , x_8)
        else:
            return cur_output
    elif state == 3 :
        cur_output,carry = shl_with_carry(vec_i)
        if carry == 1:
            cur_output = xor_vec(cur_output,vec_i)
            return xor_vec(cur_output,x_8)
        else:
            return xor_vec(cur_output,vec_i)
    else:
        return None


def sub_bytes(state_128: int) -> int:
    S_BOX = [
    0x63, 0x7c, 0x77, 0x7b, 0xf2, 0x6b, 0x6f, 0xc5, 0x30, 0x01, 0x67, 0x2b, 0xfe, 0xd7, 0xab, 0x76,
    0xca, 0x82, 0xc9, 0x7d, 0xfa, 0x59, 0x47, 0xf0, 0xad, 0xd4, 0xa2, 0xaf, 0x9c, 0xa4, 0x72, 0xc0,
    0xb7, 0xfd, 0x93, 0x26, 0x36, 0x3f, 0xf7, 0xcc, 0x34, 0xa5, 0xe5, 0xf1, 0x71, 0xd8, 0x31, 0x15,
    0x04, 0xc7, 0x23, 0xc3, 0x18, 0x96, 0x05, 0x9a, 0x07, 0x12, 0x80, 0xe2, 0xeb, 0x27, 0xb2, 0x75,
    0x09, 0x83, 0x2c, 0x1a, 0x1b, 0x6e, 0x5a, 0xa0, 0x52, 0x3b, 0xd6, 0xb3, 0x29, 0xe3, 0x2f, 0x84,
    0x53, 0xd1, 0x00, 0xed, 0x20, 0xfc, 0xb1, 0x5b, 0x6a, 0xcb, 0xbe, 0x39, 0x4a, 0x4c, 0x58, 0xcf,
    0xd0, 0xef, 0xaa, 0xfb, 0x43, 0x4d, 0x33, 0x85, 0x45, 0xf9, 0x02, 0x7f, 0x50, 0x3c, 0x9f, 0xa8,
    0x51, 0xa3, 0x40, 0x8f, 0x92, 0x9d, 0x38, 0xf5, 0xbc, 0xb6, 0xda, 0x21, 0x10, 0xff, 0xf3, 0xd2,
    0xcd, 0x0c, 0x13, 0xec, 0x5f, 0x97, 0x44, 0x17, 0xc4, 0xa7, 0x7e, 0x3d, 0x64, 0x5d, 0x19, 0x73,
    0x60, 0x81, 0x4f, 0xdc, 0x22, 0x2a, 0x90, 0x88, 0x46, 0xee, 0xb8, 0x14, 0xde, 0x5e, 0x0b, 0xdb,
    0xe0, 0x32, 0x3a, 0x0a, 0x49, 0x06, 0x24, 0x5c, 0xc2, 0xd3, 0xac, 0x62, 0x91, 0x95, 0xe4, 0x79,
    0xe7, 0xc8, 0x37, 0x6d, 0x8d, 0xd5, 0x4e, 0xa9, 0x6c, 0x56, 0xf4, 0xea, 0x65, 0x7a, 0xae, 0x08,
    0xba, 0x78, 0x25, 0x2e, 0x1c, 0xa6, 0xb4, 0xc6, 0xe8, 0xdd, 0x74, 0x1f, 0x4b, 0xbd, 0x8b, 0x8a,
    0x70, 0x3e, 0xb5, 0x66, 0x48, 0x03, 0xf6, 0x0e, 0x61, 0x35, 0x57, 0xb9, 0x86, 0xc1, 0x1d, 0x9e,
    0xe1, 0xf8, 0x98, 0x11, 0x69, 0xd9, 0x8e, 0x94, 0x9b, 0x1e, 0x87, 0xe9, 0xce, 0x55, 0x28, 0xdf,
    0x8c, 0xa1, 0x89, 0x0d, 0xbf, 0xe6, 0x42, 0x68, 0x41, 0x99, 0x2d, 0x0f, 0xb0, 0x54, 0xbb, 0x16
]


    """
    Python equivalent of your Verilog subBytes module:

      for(i=0; i<128; i=i+8)
          out[i +: 8] = SBOX(in[i +: 8])

    This means byte 0 is bits [7:0] (LSB), byte 15 is bits [127:120] (MSB).
    """
    state_128 &= (1 << 128) - 1  # keep only 128 bits (optional safety)

    out = 0
    for byte_index in range(16):
        b_in = (state_128 >> (8 * byte_index)) & 0xFF
        b_out = S_BOX[b_in]
        out |= (b_out << (8 * byte_index))
    return out




def Muxcolunms(Matrix_4_4):
    """"the fumction will get matrix 4_4 , do the logic and 
        the output will be 4_4 matrix"""
    new_matrix = np.zeros((4, 4, 8), dtype=np.uint8)
    zero_vec = [0]*8
    
    matrix = np.array([[2,3,1,1],
                      [1,2,3,1],
                      [1,1,2,3],
                      [3,1,1,2]])
    
    for i in range(4):
        for j in range(4):
            output_mux = zero_vec*4
            cur_res = [0,0,0,0,0,0,0,0]
            for k in range(4):
                output_mux[k]=speicael_mux(matrix[i, k], Matrix_4_4[k, j])
                #print("len output mux is ",len(output_mux[k]))
                cur_res = xor_vec(output_mux[k],cur_res)
                #print("len cur_res is:",len(cur_res))

            new_matrix[i,j] = cur_res
            

    return new_matrix

def to_hex128(x: int) -> str:
    return f"0x{x & ((1<<128)-1):032x}"


def shift_rows_picture_order(x: int) -> int:
    # interpret x as 16 bytes in the SAME order as the hex string is written (MSB→LSB),
    # then make 4 rows of 4 bytes, shift rows, and pack back.

    # bytes in display order: [d4, e0, b8, 1e, 27, bf, ... , e5, 30]
    b = [(x >> (8*(15-i))) & 0xFF for i in range(16)]  # MSB first

    # 4x4 row-major matrix (like the picture)
    state = [b[i*4:(i+1)*4] for i in range(4)]

    # ShiftRows (row r shifted left by r)
    state = [row[r:] + row[:r] for r, row in enumerate(state)]

    # pack back to int (MSB first)
    out = 0
    for row in state:
        for byte in row:
            out = (out << 8) | byte
    return out

def int128_to_state_matrix_row_major(x: int) -> np.ndarray:

    x &= (1 << 128) - 1
    bytes_msb_first = [(x >> (8*(15-i))) & 0xFF for i in range(16)]
    return np.array(bytes_msb_first, dtype=np.uint8).reshape(4, 4)



def golden_model (vec_i):
    sb = sub_bytes(vec_i)
    sr = shift_rows_picture_order(sb)
    matrix_4_4_bytes = int128_to_state_matrix_row_major(sr)
    matrix_4_4_bits = hex_matrix_to_binary(matrix_4_4_bytes)
    mix_out_bin = Muxcolunms(matrix_4_4_bits)
    mix_out_hex = binary_matrix_to_hex(mix_out_bin)

  

    
    return mix_out_bin , mix_out_hex


if __name__ == "__main__":
    vectors1 = [
    0b10001101001111010000011101110010001001100100111010100000101100101010001111000101011011100001000000001111000110011111010100110000, 

    0b10001011010011011110011110110101010111101100101001101101101101101011000010101001110010110001010001011011111001001001110011011111, 

    0b10000100010101101010111010111011010001011110001100111011111010111110001001111110010001000100000100101011010011100100000001000000, 

    0b10011101110100101111000110001010100100001100010011100011000000111010011001001110010101011111110010100100111111111001010001011101, 

    0b10001010110010111100001000011101011100100110000100101010011010100001100001110011101100010001011000000111001101110011010100111111, 

    0b10101010101001010111011000100011110100111110010001010101101010001011101111100000101011101001000000101101000000101100010000100101, 

    0b01101110111100111100111110000010100111011010110010000001010110110100101011100000111000011111001011100100011110101110011100110001, 

    0b00100010001101010110101111001101111000100101101101110110011001000001110011010110111010000010101110111110010110100001011011101010, 

    0b10101101011100010000101010010001011000001111101011010001111101100010100100001101001001001001011000010110011111010010100001010101, 

    0b11100000110110000010000001110110001111111101001110010110101110001011110100011011000011000001010000110100010011000001101110000001,

    0b10001001101101100011001101110111100111111001011111011110111011010111001001001001101010011000001010001111011001100000101111011001, 

    0b01111010000100110101000000010100011000010010110101101000011111011001000011000001011110111000110010011001111000001010011101001011, 

    0b01110111010100010110011101111100011110011101101110111101011100000000001111010011010111101010000011101111001111101110111101001100, 

    0b01010110000111001000010101100001010111011001100100101010100111011001010011111010010100110001110101111111011100010001101100010110, 

    0b10011101010000010011111110111001001010100010111100100101011100100010010011101111010000001001001111000100001001101111001001000101
]
    
    vectors2 = [0b00101110000101101100011000000011001100101011011000100100011000001010100100110000011111110110111010000001001110001100000000111111,
                
                0b00001001000001001111000111011001111101001100110111101011110111010000101111001100111000100000111101010001101101100111100111001010,

                0b11111000011110011101001010001000101110111000101000111111011100010100111111000010000010001001101110100000111001011000011100001000,

                0b00101001001110001001011000111000000010101111110110100001100001101101100010011000011010110101100011110000010011001011111101011100,
                 
                0b10111000010011101100110111011111000111000011111111001101001101001000001110010111010011001110101001011010101111100000110001000000,
                
                0b00101100011111001110111101100011001011110010101010100101011001111000111000111001001000010110001000111111101101100011101111101011,
                
                0b00111100101110111010010111111011110011110101111010110000010000001001110010001111111101111111110000011010010000111100111011100000,
                
                0b11111011011010101001111010000101110110001010000101100000101001010001101110101000000000111001101010011001111011100010110011110001,
                
                0b00110111000100011001100100000110000110010000011101010001001001101100011010011110010100011111111111010110100011110101000111110110,
                
                0b01000111111000111000101111000110001101001101010011001010011100111110001011010110001011101001010001101000101010110111000000101001,
                
                0b01010010011100001001011000011010001011111101111101001001010000010111110011100101101000001011010110011000001110001111100000001000,
                
                0b01010100001101100000000111110111111101101010100001000101111100011010111011011001101000011110100111000000110010010110111010011101,
                
                0b00001010111100100101000100011101000111001011110001011000011110111110111001110001001010000010000010101110010001000101111111100111,
                
                0b11101101001101001100110000100001001100010101011111101110111001101101110001101001000000101010000011111100000010101100100111001001,
                
                0b00110001000000111100001110011010101100000101100111011000111110000001010001011111000100000010010010101010111110111011001010101111,
                
                0b00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,
                
                0b11111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111]
    W =32
    file_path = r"C:\Users\Omri\studies\courses\Year_D\synthesis\Lab_final\Lab_2\TB\golden_model_questa_out.memb"
    with open(file_path, "w") as f:
        for i, vec_i in enumerate(vectors2):
            mix_out_bin , mix_out_hex = golden_model(vec_i)
            flat_bits = np.asarray(mix_out_bin).flatten()

            input_hex = f"0x{vec_i:032x}"
            print(f"Input Hex : {input_hex}")
            print(f"mix_out {i}:\n{np.vectorize(lambda x: f'0x{x:02x}')(mix_out_hex)}")
            print("-" * 40)
            line = ''.join(str(int(bit)) for bit in flat_bits)
            f.write(line + "\n")

