// Your code
module CHIP(clk,
            rst_n,
            // For mem_D
            mem_wen_D,
            mem_addr_D,
            mem_wdata_D,
            mem_rdata_D,
            // For mem_I
            mem_addr_I,
            mem_rdata_I,
            );

    input         clk, rst_n ;
    // For mem_D
    output        mem_wen_D  ;
    output [31:0] mem_addr_D ;
    output [31:0] mem_wdata_D;
    input  [31:0] mem_rdata_D;
    // For mem_I
    output [31:0] mem_addr_I ;
    input  [31:0] mem_rdata_I;

    
    
    //---------------------------------------//
    // Do not modify this part!!!            //
    // Exception: You may change wire to reg //
    reg    [31:0] PC          ;              //
    reg   [31:0] PC_nxt      ;              //
    reg          regWrite    ;              //
    wire   [ 4:0] rs1, rs2, rd;              //
    wire   [31:0] rs1_data    ;              //
    wire   [31:0] rs2_data    ;              //
    reg   [31:0] rd_data     ;              //
    //---------------------------------------//

    // Todo: other wire/reg
    

    //parameter
    parameter auipc=3'd0;
    parameter mem_read=3'd1;
    parameter mem_write=3'd2;
    parameter jal=3'd3;
    parameter jalr=3'd4;
    parameter r_type=3'd5;
    parameter i_type=3'd6;
    parameter branch=3'd7;

    // control sig
    wire [2:0] mode;
    wire       alu_zero;
    wire       alu_positive;
    wire       alu_negative;
    reg        mem_w;
    wire       alu_ready;
    wire [3:0] alu_mode;
    // instruction used
    reg     [31:0]  input2;
    wire    [24:0]  imm;
    wire    [31:0]  extended_imm;
    wire    [6:0]   op;
    wire    [2:0]   funct3;
    wire    [6:0]   funct7;

    //store data
    wire    [31:0]  alu_result;
    

    assign op = mem_rdata_I[6:0];
    assign rd = mem_rdata_I[11:7];
    assign funct3 = mem_rdata_I[14:12];
    assign rs1 = mem_rdata_I[19:15];
    assign rs2 = mem_rdata_I[24:20];
    assign funct7 = mem_rdata_I[31:25];
    assign imm = mem_rdata_I[31:7];


    
    //---------------------------------------//
    // Do not modify this part!!!            //
    reg_file reg0(                           //
        .clk(clk),                           //
        .rst_n(rst_n),                       //
        .wen(regWrite),                      //
        .a1(rs1),                            //
        .a2(rs2),                            //
        .aw(rd),                             //
        .d(rd_data),                         //
        .q1(rs1_data),                       //
        .q2(rs2_data));                      //
    //---------------------------------------//

    // Todo: any combinational/sequential circuit

    //get mode from op
    control Control(op, mode);

    //calculate extended_imm 
    immgen Immgen(mode, imm, extended_imm);

    //get alu operation
    decide_alu_mode Decide_alu_mode(mode, funct3, funct7, alu_mode);
    
    //calculate data 
    always @(*) begin
        case(mode) 
            auipc:begin
                input2=rs2_data;
                rd_data=PC+extended_imm;
                regWrite=1'd1;
                mem_w=1'd0;
            end
            branch:begin 
                input2=rs2_data;
                rd_data=alu_result;
                regWrite=1'd0;
                mem_w=1'd0;
            end
            jal:begin
                input2=extended_imm;
                rd_data = PC+32'd4; 
                regWrite=1'd1;
                mem_w=1'd0;
            end
            jalr:begin
                input2=extended_imm;
                rd_data=PC+32'd4;
                regWrite=1'd1;
                mem_w=1'd0;
            end
            mem_read:begin
                input2=extended_imm;
                rd_data = mem_rdata_D;
                regWrite=1'd1;
                mem_w=1'd0;
            end
            mem_write:begin
                input2=extended_imm;
                rd_data = mem_rdata_D;
                regWrite=1'd0;
                mem_w=1'd1;
            end
            r_type:begin
                input2=rs2_data;
                rd_data=alu_result;
                regWrite=1'd1;
                mem_w=1'd0;
            end
            i_type:begin
                input2=extended_imm;
                rd_data=alu_result;
                regWrite=1'd1;
                mem_w=1'd0;
            end
            default: begin
                regWrite=1'd0;
                mem_w=1'd0;
            end
        endcase
    end

    //calculate PC
    always @(*)begin
        if (alu_ready)begin
            case(mode) 
                auipc:PC_nxt=PC+32'd4;
                branch:begin
                    if (funct3==3'b000)//beq
                        PC_nxt= alu_zero ? (PC+(extended_imm<<1)) : (PC+32'd4);
                    else if (funct3==3'b101)//bge
                        PC_nxt= (alu_zero||alu_positive) ? (PC+(extended_imm<<1)) : (PC+32'd4);
                    else if(funct3==3'b001)//bne
                        PC_nxt= !alu_zero ? (PC+(extended_imm<<1)) : (PC+32'd4);
                    else if (funct3==3'b100)//blt
                        PC_nxt=alu_negative ? (PC+(extended_imm<<1)) : (PC+32'd4);
                    else
                        PC_nxt=PC+32'd4;
                end
                jal:PC_nxt=PC+(extended_imm<<1); 
                jalr:PC_nxt=alu_result; 
                mem_read:PC_nxt=PC+32'd4;
                mem_write:PC_nxt=PC+32'd4;
                r_type:PC_nxt=PC+32'd4;
                i_type:PC_nxt=PC+32'd4;
                default: PC_nxt=PC;
            endcase
        end
        else PC_nxt=PC;
    end

    basic_alu Basic_alu(clk, rst_n, rs1_data, input2, alu_mode, alu_result, alu_ready, alu_zero, alu_positive, alu_negative);

    //output
    assign mem_wen_D = mem_w;
    assign mem_addr_D = alu_result;
    assign mem_wdata_D =  rs2_data;
    assign mem_addr_I = PC;

    always @(posedge clk or negedge rst_n ) begin
        if (!rst_n) begin
            PC <= 32'h00010000; // Do not modify this value!!!
            
        end
        else if (alu_ready) begin
            PC <= PC_nxt;
            
        end
    end
endmodule

module control(op, mode);
    parameter auipc=3'd0;
    parameter mem_read=3'd1;
    parameter mem_write=3'd2;
    parameter jal=3'd3;
    parameter jalr=3'd4;
    parameter r_type=3'd5;
    parameter i_type=3'd6;
    parameter branch=3'd7;

    input [6:0]op;

    output reg [2:0] mode;

    always @(*) begin
        case(op)
            7'b0110011:mode=r_type;
            7'b0010011:mode=i_type;
            7'b1100011:mode=branch;
            7'b0000011:mode=mem_read;
            7'b0100011:mode=mem_write;
            7'b1101111:mode=jal;
            7'b1100111:mode=jalr;
            7'b0010111:mode=auipc;
            default: mode=auipc;
        
        endcase
    end


endmodule

module immgen(mode, instruc, imm);
    input [2:0]mode;
    input [24:0] instruc;
    output [31:0] imm;

    parameter auipc=3'd0;
    parameter mem_read=3'd1;
    parameter mem_write=3'd2;
    parameter jal=3'd3;
    parameter jalr=3'd4;
    parameter r_type=3'd5;
    parameter i_type=3'd6;
    parameter branch=3'd7;

    reg [31:0] result;
    assign imm=result;

    always @(*) begin
        case(mode)
            r_type: result = 0;
            i_type: result = {{20{instruc[24]}}, instruc[24:13]};
            jalr: result = {{20{instruc[24]}}, instruc[24:13]};
            mem_read: result = {{20{instruc[24]}}, instruc[24:13]};
            mem_write: result = {{20{instruc[24]}}, instruc[24:18], instruc[4:0]};
            branch: result = {{20{instruc[24]}}, instruc[24], instruc[0], instruc[23:18], instruc[4:1]};
            jal: result = {{12{instruc[24]}}, instruc[24], instruc[12:5], instruc[13], instruc[23:14]};
            auipc:result={instruc[24:5] ,12'b0};
            default: result = 0;
        endcase
    end

endmodule


module decide_alu_mode(mode, funct3, funct7, alu_mode);
    input [2:0]mode;
    input [2:0]funct3;
    input [6:0]funct7;
    output reg [3:0]alu_mode;

    parameter auipc=3'd0;
    parameter mem_read=3'd1;
    parameter mem_write=3'd2;
    parameter jal=3'd3;
    parameter jalr=3'd4;
    parameter r_type=3'd5;
    parameter i_type=3'd6;
    parameter branch=3'd7;

    parameter Add=4'd0;
    parameter Sub=4'd1;
    parameter Sll=4'd2;
    parameter Slt=4'd3;
    parameter Sltu=4'd4;
    parameter Xor=4'd5;
    parameter Srl=4'd6;
    parameter Sra=4'd7;
    parameter Or=4'd8;
    parameter And=4'd9;
    parameter Mul=4'd10;
    parameter Div=4'd11;

    always @(*)begin
        case(mode)
            r_type: begin
                if (funct7 == 7'b0000001)begin
                    alu_mode = (funct3==3'b000) ? Mul : Div;
                end
                else begin
                    case(funct3)
                        3'b000: alu_mode = (funct7 == 0) ? Add:Sub;
                        3'b001: alu_mode = Sll;
                        3'b010: alu_mode = Slt;
                        3'b011: alu_mode = Sltu;
                        3'b100: alu_mode = Xor;
                        3'b101: alu_mode = (funct7 == 0) ? Srl : Sra;
                        3'b110: alu_mode = Or;
                        3'b111: alu_mode = And;
                        default: alu_mode=Add;
                    endcase
                end
            end
            i_type: begin
                case(funct3)
                    3'b000: alu_mode = Add;    // addi
                    3'b001: alu_mode = Sll;    // slli
                    3'b010: alu_mode = Slt;    // slti
                    3'b011: alu_mode = Sltu;   // sltiu
                    3'b100: alu_mode = Xor;    // xori
                    3'b101: alu_mode = (funct7 == 0) ? Srl : Sra; // srli, srai
                    3'b110: alu_mode = Or;     // or
                    3'b111: alu_mode = And;    // andi
                    default: alu_mode=Add;
                endcase
            end
            branch: alu_mode=Sub;
            jalr: alu_mode=Add;
            mem_write: alu_mode=Add;
            default: alu_mode=Add;
        endcase
    end

endmodule
module basic_alu(clk, rst_n, input1, input2, alu_mode, result, alu_ready, alu_zero, alu_positive, alu_negative);
    input   clk;
    input   rst_n;
    input   [31:0]  input1;
    input   [31:0]  input2;
    input   [3:0]   alu_mode; 
    output  [31:0]  result;
    output          alu_ready;
    output          alu_zero;
    output          alu_positive;
    output          alu_negative;
    wire [63:0] muldiv_result;
    wire [1:0] mode;
    reg valid;
    wire ready;
    reg [1:0] mode_in;
    reg [31:0] alu_result;
    

    parameter Add=4'd0;
    parameter Sub=4'd1;
    parameter Sll=4'd2;
    parameter Slt=4'd3;
    parameter Sltu=4'd4;
    parameter Xor=4'd5;
    parameter Srl=4'd6;
    parameter Sra=4'd7;
    parameter Or=4'd8;
    parameter And=4'd9;
    parameter Mul=4'd10;
    parameter Div=4'd11;
    
    assign alu_ready = ((alu_mode==Mul)||(alu_mode==Div)) ? ready: 1'd1;
    // assign alu_ready=1;
    assign mode=mode_in;
    assign alu_zero = (alu_mode == Sub) ? (alu_result == 0) : 0;
    assign alu_positive =   (alu_mode == Sub) ? ($signed(alu_result) > 0) : 0;
    assign alu_negative =   (alu_mode == Sub) ? ($signed(alu_result) < 0) : 0;
    assign result = alu_ready ? alu_result : 0;

    always @(*) begin
        case(alu_mode)
            Mul:begin
                mode_in=0;
                valid=1'd1;
            end
            Div:begin
                mode_in=1'd1;
                valid=1'd1;
            end
            default:begin
                mode_in=0;
                valid=0;
            end
        endcase
    end
        
    MulDiv mulDiv(clk, rst_n, valid, ready, mode, input1, input2, muldiv_result);

    always @(*) begin
        case(alu_mode)
            Add: alu_result = input1 + input2;
            Sub: alu_result = input1 - input2;
            Sll: alu_result = input1 << input2;
            Slt: begin
                if(input1[31] ^ input2[31]) alu_result = input1[31] == 1;
                else alu_result = input1[31] == 0 ? input1 < input2 : input1 > input2;
            end
            Sltu: alu_result = input1 < input2;
            Xor: alu_result = input1 ^ input2;
            Srl: alu_result = input1 >>> input2;
            Sra: alu_result = input1 >> input2;
            Or: alu_result = input1 | input2;
            And: alu_result = input1 & input2;
            Mul: alu_result = muldiv_result[31:0];
            Div: alu_result = muldiv_result[31:0];
            default: alu_result=0;
            
        endcase
    end

endmodule

module reg_file(clk, rst_n, wen, a1, a2, aw, d, q1, q2);

    parameter BITS = 32;
    parameter word_depth = 32;
    parameter addr_width = 5; // 2^addr_width >= word_depth

    input clk, rst_n, wen; // wen: 0:read | 1:write
    input [BITS-1:0] d;
    input [addr_width-1:0] a1, a2, aw;

    output [BITS-1:0] q1, q2;

    reg [BITS-1:0] mem [0:word_depth-1];
    reg [BITS-1:0] mem_nxt [0:word_depth-1];

    integer i;

    assign q1 = mem[a1];
    assign q2 = mem[a2];

    always @(*) begin
        for (i=0; i<word_depth; i=i+1)
            mem_nxt[i] = (wen && (aw == i)) ? d : mem[i];
    end

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            mem[0] <= 0;
            for (i=1; i<word_depth; i=i+1) begin
                case(i)
                    32'd2: mem[i] <= 32'hbffffff0;
                    32'd3: mem[i] <= 32'h10008000;
                    default: mem[i] <= 32'h0;
                endcase
            end
        end
        else begin
            mem[0] <= 0;
            for (i=1; i<word_depth; i=i+1)
                mem[i] <= mem_nxt[i];
        end
    end
endmodule

module MulDiv(clk, rst_n, valid, ready, mode, in_A, in_B, out);

    // Definition of ports
    input         clk, rst_n;
    input         valid;
    input         mode; // mode: 0: mulu, 1: divu, 2: and, 3: avg
    output        ready;
    input  [31:0] in_A, in_B;
    output [63:0] out;

    // Definition of states
    parameter IDLE = 3'd0;
    parameter MUL  = 3'd1;
    parameter DIV  = 3'd2;
    parameter OUT = 3'd3;


    // Todo: Wire and reg if needed
    reg  [ 2:0] state, state_nxt;
    reg  [ 4:0] counter, counter_nxt;
    reg  [63:0] shreg, shreg_nxt;
    reg  [31:0] alu_in, alu_in_nxt;
    reg  [32:0] alu_out;

    // Todo: Instatiate any primitives if needed
    reg [31:0] temp;
    // Todo 5: Wire assignments
    assign out=shreg;
    assign ready = (state == OUT) ? 1'b1 : 1'b0; 
    // Combinational always block
    // Todo 1: Next-state logic of state machine
    always @(*) begin
        case(state)
            IDLE: begin
                if (valid) state_nxt = mode == 0 ? MUL : DIV;
                else state_nxt = IDLE;

            end
            MUL : begin
                if (counter == 5'd31)
                    state_nxt=OUT;
                else
                    state_nxt=MUL;
            end
            DIV :begin
                if (counter == 5'd31)
                    state_nxt=OUT;
                else
                    state_nxt=DIV;
            end
            OUT : state_nxt = IDLE;
            default :state_nxt=state;
        endcase
    end

    // Todo 2: Counter
    always @(*) begin
        case(state)
            MUL:begin
                counter_nxt=counter+5'd1;
            end
            DIV:begin
                counter_nxt=counter+5'd1;
            end
            OUT:begin
                counter_nxt=5'd0;
            end
            default:counter_nxt=0;
        endcase
    end

    // ALU input
    always @(*) begin
        case(state)
            IDLE: begin
                if (valid) alu_in_nxt = in_B;
                else       alu_in_nxt = 0;
            end
            OUT : alu_in_nxt = 0;
            default: alu_in_nxt = alu_in;
        endcase
    end

    // Todo 3: ALU output
    always @(*) begin
        case(state)
            MUL:begin
                if (shreg[0]) begin
                    alu_out=alu_in+shreg[63:32];
                end
                else begin
                    alu_out=shreg[63:32];
                end
            end
            DIV:begin
                temp=shreg[63:32];
                if ($unsigned(temp)>$unsigned(alu_in)) begin
                    alu_out=shreg[63:32]-alu_in;
                    alu_out[32]=1'd1;
                end
                else begin
                    alu_out=shreg[63:32];
                    alu_out[32]=1'd0;
                end
            end
            default:alu_out=0;
        endcase
    end
    // Todo 4: Shift register
    always @(*) begin
        case(state)
            IDLE:begin
                if (valid)
                    if (mode == 1) shreg_nxt = {31'b0, in_A, 1'b0};
                    else shreg_nxt={32'd0,in_A};
                else
                shreg_nxt=64'd0;
            end
            MUL:begin
                shreg_nxt={alu_out,shreg[31:1]};
            end
            DIV:begin
                if (counter==5'd31) 
                    shreg_nxt={1'd0,alu_out[30:0],shreg[30:0],alu_out[32]};
                else
                    shreg_nxt={alu_out[30:0],shreg[31:0],alu_out[32]};
            end
            default shreg_nxt=shreg;
        endcase
    end
    // Todo: Sequential always block
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            state <= IDLE;
            counter <=5'd0;
            shreg <=32'd0;
            alu_in <=32'd0;
        end
        else begin
            counter <=counter_nxt;
            state <= state_nxt;
            shreg <= shreg_nxt;
            alu_in <= alu_in_nxt;
        end
    end

endmodule
