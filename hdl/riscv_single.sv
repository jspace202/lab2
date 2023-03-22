// riscvsingle.sv

// RISC-V single-cycle processor
// From Section 7.6 of Digital Design & Computer Architecture
// 27 April 2020
// David_Harris@hmc.edu 
// Sarah.Harris@unlv.edu

// run 210
// Expect simulator to print "Simulation succeeded"
// when the value 25 (0x19) is written to address 100 (0x64)

//   Instruction  opcode    funct3    funct7
//   add          0110011   000       0000000 - atp
//   sub          0110011   000       0100000 - atp
//   and          0110011   111       0000000 - given
//   or           0110011   110       0000000 - given
//   slt          0110011   010       0000000 - given
//   addi         0010011   000       immediate - atp
//   andi         0010011   111       immediate - given
//   ori          0010011   110       immediate - given
//   slti         0010011   010       immediate - given
//   beq          1100011   000       immediate - atp
//   lw	          0000011   010       immediate - atp
//   sw           0100011   010       immediate - atp
//   jal          1101111   immediate immediate - atp

// ----------------------TO DO---------------------------
//   auipc        0010111   immediate immediate - atp
//   bge          1100011   101       immediate - atp
//   bgeu         1100011   111       immediate - all tests pass
//   blt          1100011   100       immediate - all tests pass
//   bltu         1100011   110       immediate - atp
//   bne          1100011   001       immediate - all tests pass
//   jalr         1100111   000       immediate - atp
//   lb           0000011   000       immediate - all tests pass
//   lbu          0000011   100       immediate - all tests pass
//   lh           0000011   001       immediate - atp
//   lhu          0000011   101       immediate - all tests pass
//   lui          0110111   immediate immediate - all tests pass
//   sb           0100011   000       immediate - atp
//   sh           0100011   001       immediate - atp
//   sll          0110011   001       0000000   - atp
//   slli         0010011   001       0000000*  - atp
//   sltiu        0010011   011       immediate - atp
//   sltu         0110011   011       0000000   - atp
//   sra          0110011   101       0100000   - atp
//   srai         0010011   101       0100000*  - atp
//   srl          0110011   101       0000000   - atp
//   srli         0010011   101       0000000*  - atp
//   xor          0110011   100       0000000   - atp
//   xori         0010011   100       immediate - atp

module testbench();

  logic clk;
  logic reset;
  logic [31:0] InstructionOut;
  logic PCReady;

  logic [31:0] WriteData;
  logic [31:0] DataAdr;
  logic MemWrite;
  logic MemStrobe;

  logic [31:0] instEcall = 32'b00000000000000000000000001110011;
  // instantiate device to be tested
  top dut(clk, reset, PCReady, WriteData, DataAdr, MemWrite, InstructionOut, MemStrobe);

  initial begin
    string memfilename;
    memfilename = {"../riscvtest/lab1-tests/addi.memfile"};
    $readmemh(memfilename, dut.imem.RAM);
    $readmemh(memfilename, dut.dmem.RAM);
  end

  
  // initialize test
  initial begin
    reset <= 1; # 22; reset <= 0;
  end

  // generate clock to sequence tests
  always begin
    clk <= 1; # 5; clk <= 0; # 5;
  end

  always @(negedge clk) 
    begin
        if(instEcall == InstructionOut) 
        begin
          $display("Simulation succeeded");
          $stop;
        end
    end

  // check results
/*  always @(negedge clk) begin
    if(MemWrite) begin
      if(DataAdr === 100 & WriteData === 25) begin
          $display("Simulation succeeded");
          $stop;
      end else if (DataAdr !== 96) begin
          $display("Simulation failed");
          $stop;
      end
    end
  end*/
endmodule // testbench

module riscvsingle (
  input  logic clk, reset, PCReady,
  output logic [31:0] PC,
  input  logic [31:0] Instr,
  output logic 	MemWrite,
  output logic [31:0] ALUResult, WriteData,
  input  logic [31:0] ReadData,
  output logic       MemStrobe
  );

  logic [3:0] ALUControl;
  logic [2:0] ImmSrc, branchctrl, loadctrl, storectrl;
  logic RegWrite, Jump, Zero, Load, Store, storeInstFlag;
  logic [1:0] ALUSrc, ResultSrc, uppImm;
  
  controller c (Instr[6:0], Instr[14:12], Instr[30], Zero, ResultSrc, MemWrite, PCSrc, RegWrite, Jump, 
                uppImm, ImmSrc, ALUControl, branchctrl, ALUSrc, Load, Store, loadctrl, storectrl, storeInstFlag, MemStrobe);
    
  datapath dp (clk, reset, PCReady, ALUSrc, ResultSrc, PCSrc, RegWrite, ImmSrc, ALUControl, Zero, PC, Instr, 
              ALUResult, WriteData, ReadData, uppImm, branchctrl, Jump, loadctrl, storectrl, storeInstFlag);
   
endmodule // riscvsingle

module controller (
  input  logic [6:0] op,
  input  logic [2:0] funct3,
  input  logic       funct7b5,
  input  logic       Zero,
  output logic [1:0] ResultSrc,
  output logic       MemWrite,
  output logic       PCSrc,
  output logic       RegWrite, Jump,
  output logic [1:0] uppImm,
  output logic [2:0] ImmSrc,
  output logic [3:0] ALUControl,
  output logic [2:0] branchctrl,
  output logic [1:0] ALUSrc,
  output logic       Load, Store,
  output logic [2:0] loadctrl, storectrl,
  output logic       storeInstFlag,
  output logic       MemStrobe);
   
  logic [1:0] ALUOp;
  logic Branch;
  logic branchflag;
   
  maindec md (op, ResultSrc, MemWrite, Branch, RegWrite, Jump, ImmSrc, ALUOp, ALUSrc, uppImm, Load, Store, MemStrobe);
  aludec ad (op[5], funct3, funct7b5, ALUOp, ALUControl, storeInstFlag);
  loaddec loaddec(Load, funct3, loadctrl);
  storedec storedec(Store, funct3, storectrl);
  branchdec branchdec (Branch, funct3, branchctrl, branchflag);

  assign PCSrc = branchflag | Jump;
  //assign PCSrc = (Branch & (Zero ^ funct3[0])) | Jump;
   
endmodule // controller

module maindec (
  input  logic [6:0] op,
  output logic [1:0] ResultSrc,
  output logic MemWrite,
  output logic Branch, 
  output logic RegWrite, Jump,
  output logic [2:0] ImmSrc,
  output logic [1:0] ALUOp,
  output logic [1:0] ALUSrc, uppImm,
  output logic       Load, Store,
  output logic      MemStrobe
  );
   
  logic [16:0] controls;
  
  // TODO: Might want to add an extra bit for DDR3 strobe (e.g., a 1 for LW and SW, a 0 for R-type, beq, I-type ALU, and JAL)
  // controls = RegWrite_ImmSrc_ALUSrc_MemWrite_ResultSrc_Branch_ALUOp_Jump_Jalr_Auipc_MemStrobe
  assign {RegWrite, ImmSrc, ALUSrc, MemWrite, ResultSrc, Branch, ALUOp, Jump, uppImm, Load, Store, MemStrobe} = controls;

  always_comb

    case(op) 

      7'b1100011: controls = 17'b0_010_00_0_00_1_01_0_00_0_0; // R–types
      7'b0110011: controls = 17'b1_xxx_00_0_00_0_10_0_00_0_0; // I–types
      7'b0000011: controls = 17'b1_000_01_0_01_0_00_0_00_1_1; // loads
      7'b0100011: controls = 17'b0_001_01_1_00_0_00_0_00_0_1; // stores
      7'b0010011: controls = 17'b1_000_01_0_00_0_10_0_00_0_0; // B-types
      7'b0110111: controls = 17'b1_100_01_0_00_0_00_0_01_0_0; // lui
      7'b0010111: controls = 17'b1_100_01_0_00_0_00_0_11_0_0; // auipc
      7'b1101111: controls = 17'b1_011_00_0_10_0_00_1_00_0_0; // jal
      7'b1100111: controls = 17'b1_000_01_0_11_0_10_1_00_0_0; // jalr
      default: controls = 17'bx_xxx_xx_x_xx_x_xx_x_xx_x_x; // ???

    endcase

endmodule // maindec

module aludec (
  input  logic opb5,
  input  logic [2:0] funct3,
  input  logic funct7b5,
  input  logic [1:0] ALUOp,
  output logic [3:0] ALUControl,
  output logic       storeInstFlag
  );

  logic RtypeSub, shiftRight;

  assign RtypeSub = funct7b5 & opb5; // TRUE for R–type subtract
  assign shiftRight = funct7b5 & (funct3 == 3'b101);

  always_comb
    case(ALUOp)
      2'b00: begin
        ALUControl = 4'b0000; // addition
        storeInstFlag = 1'b0;
        end
      2'b01: begin
        ALUControl = 4'b0001; // subtraction
        storeInstFlag = 1'b0;
        end
      default: case(funct3) // R–type or I–type ALU
          3'b000: begin
            if (RtypeSub)
            ALUControl = 4'b0001; // sub
            else
            ALUControl = 4'b0000; // add, addi
            storeInstFlag = 1'b0;
            end
          3'b010: begin
            ALUControl = 4'b0101; // slt, slti
            storeInstFlag = 1'b0;
            end
          3'b110: begin
            ALUControl = 4'b0011; // or, ori
            storeInstFlag = 1'b0;
            end
          3'b111: begin
            ALUControl = 4'b0010; // and, andi
            storeInstFlag = 1'b0;
            end
          3'b001: begin
            ALUControl = 4'b0100; // sll, slli
            storeInstFlag = 1'b1;
            end
          3'b011: begin
            ALUControl = 4'b0110; // sltu, sltiu
            storeInstFlag = 1'b0;
            end
          3'b101: begin
            if(shiftRight) ALUControl = 4'b0111; // sra, srai
            else ALUControl = 4'b1000; // srl, srli
            storeInstFlag = 1'b1;
              end
          3'b100: begin
            ALUControl = 4'b1001; 
            storeInstFlag = 1'b0;
            end
          default: begin
            ALUControl = 4'bxxxx; // ???
            storeInstFlag = 1'bx;
            end
        endcase // case (funct3)      

    endcase // case (ALUOp)
   
endmodule // aludec

module loaddec (input logic Load,
                input logic [2:0] funct3,
                output logic [2:0] loadctrl);

    always_comb
    if(Load)begin
    case(funct3)
      3'b000: loadctrl = 3'b000;
      3'b001: loadctrl = 3'b001;
      3'b010: loadctrl = 3'b010;
      3'b100: loadctrl = 3'b100;
      3'b101: loadctrl = 3'b101;
      default: loadctrl = 3'bx;
    endcase
    end
    else loadctrl = 3'bx;

endmodule

module storedec (input logic Store,
                input logic [2:0] funct3,
                output logic [2:0] storectrl);

    always_comb
      if(Store)begin
      case(funct3)
        3'b000: storectrl = 3'b000;
        3'b001: storectrl = 3'b001;
        3'b010: storectrl = 3'b010;
        default: storectrl = 3'bx;
      endcase
      end
      else storectrl = 3'bx;

endmodule

module branchdec (input logic Branch,
             input logic [2:0] funct3,
             output logic [2:0] branchctrl,
             output logic branchflag
            );

    always_comb
    if(Branch)begin
    case(funct3)
      3'b001: begin branchctrl = 3'b001;
              branchflag = 1'b1; end
      3'b000: begin branchctrl = 3'b000;
              branchflag = 1'b1; end
      3'b100: begin branchctrl = 3'b100;
              branchflag = 1'b1; end
      3'b101: begin branchctrl = 3'b101;
              branchflag = 1'b1; end
      3'b110: begin branchctrl = 3'b110;
              branchflag = 1'b1; end
      3'b111: begin branchctrl = 3'b111;
              branchflag = 1'b1; end
      default: branchctrl = 3'bx;
    endcase
    end
    else branchflag = 1'b0;

endmodule

module datapath (
  input  logic       clk, reset, PCReady,
  input  logic [1:0] ALUSrc, ResultSrc,
  input  logic       PCSrc,
  input  logic       RegWrite,
  input  logic [2:0] ImmSrc,
  input  logic [3:0] ALUControl,
  output logic        Zero,
  output logic [31:0] PC,
  input  logic [31:0] Instr,
  output logic [31:0] ALUResult, WriteData,
  input  logic [31:0] ReadData,
  input  logic [1:0] uppImm,
  input  logic [2:0] branchctrl,
  input  logic       Jump,
  input  logic [2:0] loadctrl, storectrl,
  input  logic       storeInstFlag);
   
  logic [31:0] PCNext, PCPlus4, PCTarget;
  logic [31:0] ImmExt;
  logic [31:0] SrcA, SrcB, SrcC;
  logic [31:0] Result;
  logic        PCSrc2;
  logic [31:0] PCTarget2, Readdata2, WriteData2;
   
  // next PC logic
 // flopenr #(32) pcreg (clk, reset, PCReady, PCNext, PC);
  flopr #(32) pcreg (clk, reset, PCNext, PC); // TODO: want to change to flopenr when implementing; only ENABLE when DDR3 is DONE
  adder  pcadd4 (PC, 32'd4, PCPlus4);
  adder  pcaddbranch (PC, ImmExt, PCTarget2);
  mux2 #(32)  pcmux (PCPlus4, PCTarget, PCSrc2, PCNext);
  branchalu branchalu (Jump, SrcA, SrcB, branchctrl, PCSrc, PCSrc2);
  PCadder PCadder (Jump, PCTarget2, ALUResult, PCTarget, ALUSrc);

  // register file logic
  regfile  rf (clk, RegWrite, Instr[19:15], Instr[24:20], Instr[11:7], Result, SrcA, WriteData2);
  extend  ext (Instr[31:7], ImmSrc, ImmExt, storeInstFlag);

  // ALU logic
  mux2 #(32)  srccmux (WriteData2, ImmExt, ALUSrc[0], SrcC);
  alu  alu (SrcA, SrcB, ALUControl, ALUResult, Zero, uppImm);
  mux3 #(32) resultmux (ALUResult, Readdata2, PCPlus4, ResultSrc, Result);
  storealu storealu (storectrl, WriteData2, ALUResult, ReadData, WriteData);
  shift12 #(32) srcbmux (SrcC, PC, uppImm, SrcB);
  loadalu loadalu (loadctrl, ReadData, ALUResult, Readdata2);

endmodule // datapath

module adder (input  logic [31:0] a, b,
              output logic [31:0] y);
  
  assign y = a + b;
   
endmodule

module PCadder (input  logic        Jump,
                input  logic [31:0] a, b,
                output logic [31:0] y,
                input  logic [1:0] ALUSrc);
  
  always_comb
  if(Jump & !ALUSrc[0] & b != 32'bx) y = a + b;
  else if (Jump & ALUSrc[0]) y = b;
  else y = a;
   
endmodule

module extend (input  logic [31:7] instr,
               input  logic [2:0]  immsrc,
               output logic [31:0] imdextend,
               input  logic        storeInstFlag);
   
  always_comb
    case(immsrc)
      // I−type
      3'b000:  begin
               if(!storeInstFlag) imdextend = {{20{instr[31]}}, instr[31:20]};
               else imdextend = {{20{instr[31]}}, instr[24:20]}; 
               end
      // S−type (stores)
      3'b001:  imdextend = {{20{instr[31]}}, instr[31:25], instr[11:7]};
      // B−type (branches)
      3'b010:  imdextend = {{20{instr[31]}}, instr[7], instr[30:25], instr[11:8], 1'b0};       
      // J−type (jal)
      3'b011:  imdextend = {{12{instr[31]}}, instr[19:12], instr[20], instr[30:21], 1'b0};
      // U-type
      3'b100:  imdextend = {{12{instr[31:12]}}, instr[31:12]};
      default: imdextend = 32'bx; // undefined
    endcase // case (immsrc)

endmodule // extend

module flopr #(parameter WIDTH = 8)(
  input  logic clk, reset,
  input logic [WIDTH-1:0]  d,
  output logic [WIDTH-1:0] q
  );
   
  always_ff @(posedge clk, posedge reset)
    if (reset) q <= 0;
    else  q <= d;
   
endmodule // flopr

module flopenr #(parameter WIDTH = 8)(
  input  logic clk, reset, en,
  input logic [WIDTH-1:0]  d,
  output logic [WIDTH-1:0] q
  );
   
  always_ff @(posedge clk, posedge reset)
    if (reset)  q <= 0;
    else if (en) q <= d;
   
endmodule // flopenr

module mux2 #(parameter WIDTH = 8)(
  input  logic [WIDTH-1:0] d0, d1,
  input logic              s,
  output logic [WIDTH-1:0] y
  );

  assign y = s ? d1 : d0;
   
endmodule // mux2

module mux3 #(parameter WIDTH = 8)(
  input logic [WIDTH-1:0] d0, d1, d2,
  input logic [1:0]       s,
  output logic [WIDTH-1:0] y
  );
   
  assign y = s[1] ? d2 : (s[0] ? d1 : d0);
   
endmodule // mux3

module shift12 #(parameter WIDTH = 8)
    (input logic [WIDTH-1:0] d0, d1,
     input logic [1:0]       s,
     output logic [WIDTH-1:0] y
    );

    assign y = s[0] ? (s[1] ? (d0 << 12) + d1 : (d0 << 12)) : d0;

endmodule

module top (
  input  logic clk, reset, PCReady
  output logic [31:0] WriteData, DataAdr,
  output logic 	MemWrite,
  output logic [31:0] InstructionOut,
  output logic MemStrobe
  );
   
  logic [31:0] 		PC, Instr, ReadData;
  
  // instantiate processor and memories
  riscvsingle rv32single (clk, reset, PCReady, PC, Instr, MemWrite, DataAdr, WriteData, ReadData, MemStrobe);
  imem imem (PC, Instr);
  dmem dmem (clk, MemWrite, DataAdr, WriteData, ReadData);
  always_comb begin
  InstructionOut = Instr;
  end
   
endmodule // top

module imem (
  input  logic [31:0] a,
  output logic [31:0] rd
  );
   
  logic [31:0] RAM[1500:0]; // TODO: Was originally RAM[63:0]
  
  assign rd = RAM[a[31:2]]; // word aligned
   
endmodule // imem

module dmem (
  input logic clk, we,
  input  logic [31:0] a, wd,
  output logic [31:0] rd
  );
   
  logic [31:0] RAM[1500:0];
  
  assign rd = RAM[a[31:2]]; // word aligned
  always_ff @(posedge clk)
    if (we) RAM[a[31:2]] <= wd;
  
endmodule // dmem

module alu (
  input  logic [31:0] a, b,
  input  logic [3:0] 	alucontrol,
  output logic [31:0] result,
  output logic 	      zero,
  input  logic [1:0] uppImm);

  logic [31:0] condinvb, sum, signop;
  logic v; // overflow
  logic isAddSub; // true when is add or subtract operation

  assign condinvb = alucontrol[0] ? ~b : b;
  assign sum = a + condinvb + alucontrol[0];
  assign isAddSub = ~alucontrol[2] & ~alucontrol[1] |
                    ~alucontrol[1] & alucontrol[0];   

  assign signop = ~(32'hFFFFFFFF >> (b & 32'h1F));

  always_comb
    case (alucontrol)
      4'b0000:  result = uppImm[0] ? (uppImm[1] ? sum : b) : sum; // add
      4'b0001:  result = sum; // subtract
      4'b0010:  result = a & b; // and
      4'b0011:  result = a | b; // or
      4'b0100:  result = a << (b & 32'h1f); // sll
      4'b0101:  result = sum[31] ^ v; // slt
      4'b0110:  result = (unsigned'(a) < b) ? 1 : 0; // srl
      4'b0111:  begin if (a[31]) result = (a >> (b & 32'h1F)) | signop;
                else result = a >> (b & 32'h1F); end // sra
      4'b1000:  result = a >> (b & 32'h1f); // sltu
      4'b1001:  result = a ^ b; // xor
      default: result = 32'bx;
    endcase

  assign zero = (result == 32'b0);
  assign v = ~(alucontrol[0] ^ a[31] ^ b[31]) & (a[31] ^ sum[31]) & isAddSub;
   
endmodule // alu

module loadalu (input logic [2:0] loadctrl,
             input logic [31:0] ReadMem, byteAddress,
             output logic [31:0] WriteMem
            );

    logic [31:0] shiftedReadMem;

    always_comb begin
      shiftedReadMem = ReadMem >> (byteAddress[1:0] * 8);
      case(loadctrl)
        3'b000: WriteMem = shiftedReadMem[7] ? (shiftedReadMem | 32'hFFFFFF00) : (shiftedReadMem & 32'h000000FF);
        3'b001: WriteMem = shiftedReadMem[15] ? (shiftedReadMem | 32'hFFFF0000) : (shiftedReadMem & 32'h0000FFFF);
        3'b010: WriteMem = ReadMem;
        3'b100: WriteMem = unsigned'(shiftedReadMem) & 32'h000000FF;
        3'b101: WriteMem = unsigned'(shiftedReadMem) & 32'h0000FFFF;
        default: WriteMem = 32'bx;
    endcase
    end

endmodule

module storealu (input logic [2:0] storectrl,
                 input logic [31:0] Regread, byteAddress, ReadMem,
                 output logic [31:0] WriteMem );

    always_comb begin
      case(storectrl)
      3'b000: begin
              if(byteAddress[1:0] == 0) WriteMem = (ReadMem & 32'hFFFFFF00) | ((Regread & 32'h000000FF));
              if(byteAddress[1:0] == 1) WriteMem = (ReadMem & 32'hFFFF00FF) | ((Regread & 32'h000000FF) << 8);
              if(byteAddress[1:0] == 2) WriteMem = (ReadMem & 32'hFF00FFFF) | ((Regread & 32'h000000FF) << 16);
              if(byteAddress[1:0] == 3) WriteMem = (ReadMem & 32'h00FFFFFF) | ((Regread & 32'h000000FF) << 24);
              end
      3'b001: begin
              if(byteAddress[1:0] == 0) WriteMem = (ReadMem & 32'hFFFF0000) | ((Regread & 32'h0000FFFF));
              if(byteAddress[1:0] == 2) WriteMem = (ReadMem & 32'h0000FFFF) | ((Regread & 32'h0000FFFF) << 16);
              end
      3'b010: WriteMem = Regread;
      default: WriteMem = 32'bx;
    endcase
    end

endmodule

module branchalu (input logic Jump,
            input logic [31:0] a, b,
            input logic [2:0] branchctrl,
            input logic       PCSource,
            output logic      PCSOut
            ); 
    always_comb
      if(PCSource & !Jump) begin
      case(branchctrl)
        3'b001: begin
                if(a != b) PCSOut = 1'b1;
                else PCSOut = 1'b0;
                end
        3'b000: begin
                if(a == b) PCSOut = 1'b1;
                else PCSOut = 1'b0;
                end
        3'b100: begin
                if(signed'(a) < signed'(b)) PCSOut = 1'b1;
                else PCSOut = 1'b0;
                end
        3'b101: begin
                if(signed'(a) >= signed'(b)) PCSOut = 1'b1;
                else PCSOut = 1'b0;
                end
        3'b110: begin
                if(unsigned'(a) < unsigned'(b)) PCSOut = 1'b1;
                else PCSOut = 1'b0;
                end
        3'b111: begin
                if(unsigned'(a) >= unsigned'(b)) PCSOut = 1'b1;
                else PCSOut = 1'b0;
                end
        default: PCSOut = 3'bx;
      endcase
      end
      else if (Jump) PCSOut = 1'b1;
      else PCSOut = 1'b0;

endmodule

module regfile (
  input logic clk, 
  input logic we3, 
  input logic [4:0] a1, a2, a3, 
  input logic [31:0] wd3, 
  output logic [31:0] rd1, rd2
  );

  logic [31:0] 		    rf[31:0];

  // three ported register file
  // read two ports combinationally (A1/RD1, A2/RD2)
  // write third port on rising edge of clock (A3/WD3/WE3)
  // register 0 hardwired to 0

  always_ff @(posedge clk)
    if (we3) rf[a3] <= wd3;	

  assign rd1 = (a1 != 0) ? rf[a1] : 0;
  assign rd2 = (a2 != 0) ? rf[a2] : 0;
   
endmodule // regfile