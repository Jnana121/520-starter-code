package miniJava.CodeGeneration;

import miniJava.ErrorReporter;
import miniJava.AbstractSyntaxTrees.*;
import miniJava.AbstractSyntaxTrees.Package;
import miniJava.CodeGeneration.x64.*;
import miniJava.CodeGeneration.x64.ISA.*;

public class CodeGenerator implements Visitor<Object, Object> {
	private Instruction _mallocFn; // at what instruction does the mallocFn start?
	private Instruction _freeFn; // at what instruction does the freeFn start?
	private InstructionList _asm; // our list of instructions that are used to make the code section
	private ErrorReporter _errors;
	private int _rbpOffset; // offset from rbp that indicates where local variables are
	private ClassDecl _currentClass;
	private List<Jmp> _returnPatches; // if return is in a function not at the end, we jump to the end
	private long _mainAddress = -1; // where is entrypoint
	private final boolean _outputAssembly = false; // debug output
	private int _staticSize; // size of the static segment
	private Stack<Integer> _blockStackSize; // used to make and remove stack space for locals

	public CodeGenerator(ErrorReporter errors) {
		this._errors = errors;
	}

	@Override
	public Object visitPackage(Package prog, Object arg) {
		// first, find the number of static variables we got
		//  also set the base offset for non-static variables
		_staticSize = 0;
		for( ClassDecl c : prog.classDeclList ) {
			int baseOffset = 0;
			for( FieldDecl f : c.fieldDeclList ) {
				if( f.isStatic ) {
					// how far away are we from the start of the static variables?
					f.bssOffset = _staticSize;
					_staticSize += f.type.getVarSize();
				} else {
					// how far are we from the start of the object's variables?
					f.objOffset = baseOffset;
					baseOffset += f.type.getVarSize();
				}
			}
			c.dynSize = baseOffset;
		}
		// round up the static size because writes can get messy if not done right
		_staticSize = ( _staticSize + 7 ) & ~7;

		_asm = new InstructionList();

		if( _outputAssembly ) {
			System.out.println("Malloc:");
			_asm.markOutputStart();
		}

		// prebuild functions
		// BEGIN MALLOC
		_mallocFn = new Push(Reg64.RBP);
		_asm.add(_mallocFn);
		_asm.add(new Mov_rmr(new ModRMSIB(Reg64.RBP,Reg64.RSP)));

		_asm.add( new Mov_rmi(new ModRMSIB(Reg64.RAX,true),0x09) ); // mmap
		_asm.add( new Xor(new ModRMSIB(Reg64.RDI,Reg64.RDI)) ); // addr=0
		_asm.add( new Mov_rmi(new ModRMSIB(Reg64.RSI,true),0x1000) ); // 4kb alloc
		_asm.add( new Mov_rmi(new ModRMSIB(Reg64.RDX,true),0x03) ); // prot read|write
		_asm.add( new Mov_rmi(new ModRMSIB(Reg64.R10,true),0x22) ); // flags= private, anonymous
		_asm.add( new Mov_rmi(new ModRMSIB(Reg64.R8,true),-1) ); // fd= -1
		_asm.add( new Xor(new ModRMSIB(Reg64.R9,Reg64.R9)) ); // offset=0
		_asm.add( new Syscall() );

		// returned value is in RAX
		_asm.add(new Mov_rmr(new ModRMSIB(Reg64.RSP,Reg64.RBP)));
		_asm.add(new Pop(Reg64.RBP));
		_asm.add(new Ret());

		if( _outputAssembly ) {
			_asm.outputFromMark();
			System.out.println("Free:");
			_asm.markOutputStart();
		}

		// BEGIN FREE
		_freeFn = new Push(Reg64.RBP);
		_asm.add(_freeFn);
		_asm.add(new Mov_rmr(new ModRMSIB(Reg64.RBP,Reg64.RSP)));

		_asm.add( new Mov_rmi(new ModRMSIB(Reg64.RAX,true), 0x0B) ); // munmap

		// addr should be in RDI
		_asm.add( new Mov_rmi(new ModRMSIB(Reg64.RSI,true),0x1000) ); // 4kb
		_asm.add(new Syscall());

		_asm.add(new Mov_rmr(new ModRMSIB(Reg64.RSP,Reg64.RBP)));
		_asm.add(new Pop(Reg64.RBP));
		_asm.add(new Ret());

		if( _outputAssembly )
			_asm.outputFromMark();

		// create a jump table for each method
		for( ClassDecl c : prog.classDeclList ) {
			for( MethodDecl m : c.methodDeclList ) {
				m.ins = new Jmp((int)0);
				_asm.add(m.ins);
			}
		}

		for( ClassDecl c : prog.classDeclList )
			c.visit(this);

		if( _mainAddress == -1 ) {
			_errors.reportError("Main method not declared");
			return null;
		}

		return null;
	}

	public void makeElf(String fname) {
		ELFMaker elf = new ELFMaker(_errors, _asm.getSize(), _staticSize + 8);
		elf.outputELF(fname, _asm.getBytes(), (long)_mainAddress);
	}

	@Override
	public Object visitClassDecl(ClassDecl cd, Object arg) {
		_currentClass = cd;

		if( _outputAssembly )
			System.out.printf("Begin class %s:\n", cd.name);

		for( MethodDecl m : cd.methodDeclList )
			m.visit(this);
		return null;
	}

	@Override
	public Object visitFieldDecl(FieldDecl fd, Object arg) {
		return null;
	}

	@Override
	public Object visitMethodDecl(MethodDecl md, Object arg) {
		_returnPatches = new ArrayList<Jmp>();
		_blockStackSize = new Stack<Integer>();
		_blockStackSize.push(0);

		if( _outputAssembly ) {
			System.out.printf("Begin Method %s::%s\n", _currentClass.name, md.name);
			_asm.markOutputStart();
		}

		// is this the main method?
		boolean isMain = false;
		if( md.name.equals("main") && md.isStatic && !md.isPrivate && md.parameterDeclList.size() == 1
				&& md.type.typeKind == TypeKind.VOID
				&& md.parameterDeclList.get(0).type instanceof ArrayType
				&& ((ArrayType)md.parameterDeclList.get(0).type).eltType instanceof ClassType
				&& ((ClassType)((ArrayType)md.parameterDeclList.get(0).type).eltType).className.spelling.equals("String") ) {

			if( _mainAddress != -1 )
				_errors.reportError("*** line ", md.posn.toString(), ": Error, duplicate main function found");
			_mainAddress = _asm.getSize();
			isMain = true;

			// Inside R15 we store the "base" of the static variables, and just never touch it again.
			if( _staticSize > 0 ) {
				_asm.add(new Sub(new ModRMSIB(Reg64.RSP,true),_staticSize));
				_asm.add(new Mov_rmr(new ModRMSIB(Reg64.R15,Reg64.RSP)));
			}
		}

		_asm.patch(md.ins.listIdx, new Jmp(md.ins.startAddress, _asm.getSize(), false) );

		_asm.add(new Push(Reg64.RBP));
		_asm.add(new Mov_rmr(new ModRMSIB(Reg64.RBP,Reg64.RSP)));

		// stack currently contains:
		// [parameters...] [return addr] [old rbp]      [next free]
		//     /\ rbp+16                     /\ rbp=rsp    /\ rbp-8

		// Note, "this" pointer (if any) is the last thing to be pushed,
		// so parameters will start at rbp+24 for non-statics
		int paramRbpOffset = md.isStatic ? 16 : 24;
		for( ParameterDecl p : md.parameterDeclList ) {
			p.rbp_offset = paramRbpOffset;
			paramRbpOffset += 8;
		}

		// next free spot is at -8
		_rbpOffset = -8;

		if( _outputAssembly )
			_asm.outputFromMark();

		visitStatementList(md.statementList);

		if( _outputAssembly )
			_asm.markOutputStart();

		// any returns now need to be patched to this "close out function" address
		for( Jmp jmp : _returnPatches )
			_asm.patch(jmp.listIdx, new Jmp(jmp.startAddress, _asm.getSize(), false));

		_asm.add(new Mov_rmr(new ModRMSIB(Reg64.RSP,Reg64.RBP)));
		_asm.add(new Pop(Reg64.RBP));

		if( isMain ) {
			// SYS_exit
			_asm.add(new Mov_rmi(new ModRMSIB(Reg64.RAX,true),60) );
			_asm.add(new Xor(new ModRMSIB(Reg64.RDI,Reg64.RDI)));
			_asm.add(new Syscall());
			_asm.add(new Ret());
			if( _outputAssembly )
				_asm.outputFromMark();
			return null;
		}

		// callee cleans up the stack
		short cleanupSize = md.isStatic ? (short)md.parameterDeclList.size() : (short)( md.parameterDeclList.size()+1);
		if( cleanupSize == 0 )
			_asm.add(new Ret());
		else
			_asm.add(new Ret(cleanupSize));

		if( _outputAssembly )
			_asm.outputFromMark();
		return null;
	}
	
	public void makeElf(String fname) {
		ELFMaker elf = new ELFMaker(_errors, _asm.getSize(), 8); // bss ignored until PA5, set to 8
		elf.outputELF(fname, _asm.getBytes(), ??); // TODO: set the location of the main method
	}
	
	private int makeMalloc() {
		int idxStart = _asm.add( new Mov_rmi(new ModRMSIB(Reg64.RAX,true),0x09) ); // mmap
		
		_asm.add( new Xor(		new ModRMSIB(Reg64.RDI,Reg64.RDI)) 	); // addr=0
		_asm.add( new Mov_rmi(	new ModRMSIB(Reg64.RSI,true),0x1000) ); // 4kb alloc
		_asm.add( new Mov_rmi(	new ModRMSIB(Reg64.RDX,true),0x03) 	); // prot read|write
		_asm.add( new Mov_rmi(	new ModRMSIB(Reg64.R10,true),0x22) 	); // flags= private, anonymous
		_asm.add( new Mov_rmi(	new ModRMSIB(Reg64.R8, true),-1) 	); // fd= -1
		_asm.add( new Xor(		new ModRMSIB(Reg64.R9,Reg64.R9)) 	); // offset=0
		_asm.add( new Syscall() );
		
		// pointer to newly allocated memory is in RAX
		// return the index of the first instruction in this method, if needed
		return idxStart;
	}
	
	private int makePrintln() {
		// TODO: how can we generate the assembly to println?
		return -1;
	}
}
