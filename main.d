import std.stdio, std.typecons, std.conv, std.string, std.range, pegged.grammar, std.file, dsl, std.exception;

mixin(grammar(`
Program:
	Prog < TypeDef* FunDef+
	TypeDef < "type" Name "=" (TupleDef / ListDef)
	TupleDef < "(" ArgDef ("," ArgDef)* ")"
	ArgDef < Name ":" TypeExpr
	ListDef < "[" TypeExpr "]"
	TypeExpr <- "Int" / Name / ListDef
    Name <~ [A-Za-z]+
	FunDef < "def" Name TupleDef FunDef* Expr "end"
	Expr < LetExpr / Single (BinOp Single)*
	Single < "(" Expr ")" / IfExpr / If0Expr / Const / FunCall / VarExpr  / ConsExpr / ListExpr
	BinOp <- "+" / "-" / "*" / "/" / "==" / "!=" / "<=" / ">=" / "<" / ">" 
	LetExpr < "let" Name ":" TypeExpr "=" Expr "in" Expr
	Const <~ "-"? [0-9]+
	VarExpr <- Name ("." Name)*
	ConsExpr < "@(" Expr "," Expr ")"
	ListExpr < "[" Expr ("," Expr)* "]"
	FunCall < Name "(" Expr ("," Expr)* ")"
	IfExpr < "if" Expr "then" Expr "else" Expr
	If0Expr < "if0" Expr "then" Expr "else" Expr
`));

Type IntType() {
	static Type t; //new TInt;
	if (t is null) t = new TInt;
	return t;
}

Type[string] types;

Type compileTypeExpr(ParseTree te) {
	enforce(te.name=="Program.TypeExpr");
	if (te.matches[0]=="Int") return IntType();
	enforce(te.children.length > 0);
	if (te.children[0].name=="Program.Name") return types[te.children[0].matches[0]];
	if (te.children[0].name=="Program.ListDef") {
		auto ty = compileTypeExpr(te.children[0].children[0]);
		return new TList(ty);
	}
	assert(0, "bad type expr");
}

ArgDef compileArgDef(ParseTree ad) {
	enforce(ad.name=="Program.ArgDef");
	enforce(ad.children.length==2);
	enforce(ad.children[0].name=="Program.Name");
	auto ty = compileTypeExpr(ad.children[1]);
	return tuple(ad.children[0].matches[0], ty);
}

ArgDef[] compileArgs(ParseTree def) {
	enforce(def.name=="Program.TupleDef");
	return def.children.map!(compileArgDef).array;
}

Type compileTypeDef(ParseTree def) {
	if (def.name=="Program.TupleDef") {
		return new TTuple( compileArgs(def) );
	} else
	if (def.name=="Program.ListDef") {
		auto ty = compileTypeExpr(def.children[0]);
		return new TList(ty);
	} 
	assert(0, "bad type def");
}

class Scope {
	Scope parent;
	ArgDef[] argdefs;
	Args args;

	this(ArgDef[] argdefs_, Args args_, Scope par) {
		argdefs = argdefs_;
		args = args_;
		parent = par;
	}

	Val findVar(string name) {
		foreach(a; argdefs)
			if (a[0]==name)
				return args.getArg(name);
		if (parent !is null) return parent.findVar(name);
		assert(0, "var not found: "~ name);
	}
}

Val compileLet(Writer w, ParseTree pt, Scope scp) {
	string name = pt.children[0].matches[0];
	Type ty = compileTypeExpr(pt.children[1]);
	ArgDef[] argdefs = [name in ty];
	return w.let(argdefs, compileExpr(w, pt.children[2], scp), (w,as) {
		compileExpr(w, pt.children[3], new Scope(argdefs, as, scp)).gen(w);
	});
}

Val compileSingle(Writer w, ParseTree pt, Scope scp) {
	enforce(pt.name=="Program.Single");
	auto ch = pt.children[0];
	switch(ch.name) {
		case "Program.Const": return num(ch.matches[0].to!int);
		case "Program.Expr": return compileExpr(w, ch, scp);
		case "Program.If0Expr": return if0( compileExpr(w, ch.children[0], scp), 
											compileExpr(w, ch.children[1], scp),
											compileExpr(w, ch.children[2], scp));
		case "Program.IfExpr":  return if0( compileExpr(w, ch.children[0], scp), 
											compileExpr(w, ch.children[2], scp),
										    compileExpr(w, ch.children[1], scp));
		case "Program.FunCall": return call(ch.children[0].matches[0], ch.children[1..$].map!(e => compileExpr(w, e, scp)).array);
		case "Program.ConsExpr": return cons( compileExpr(w, ch.children[0], scp),  compileExpr(w, ch.children[1], scp) );
		case "Program.ListExpr": return list( ch.children.map!(e => compileExpr(w, e, scp)).array );
		case "Program.VarExpr":
			string[] names = ch.children.map!(c => c.matches[0]).array;
			Val v = scp.findVar(names[0]);
			foreach(nm; names[1..$])
				v = v.getMemb(nm);
			return v;
		default: assert(0, "bad single expr");
	}
}

Val compileExpr(Writer w, ParseTree pt, Scope scp) {
	enforce(pt.name=="Program.Expr");
	if (pt.children[0].name=="Program.LetExpr")
		return compileLet(w, pt.children[0], scp);
	enforce(pt.children[0].name=="Program.Single");
	Val v = compileSingle(w, pt.children[0], scp);
	int i = 0;
	while(i+2 < pt.children.length) {
		Val v2 = compileSingle(w, pt.children[i+2], scp);
		switch(pt.children[i+1].matches[0]) {
			case "+": v = v + v2; break;
			case "-": v = v - v2; break;
			case "*": v = v * v2; break;
			case "/": v = v / v2; break;
			case "==": v = eq(v, v2); break;
			case "!=": v = not(eq(v, v2)); break;
			case ">": v = gt(v, v2); break;
			case ">=": v = gte(v, v2); break;
			case "<": v = gt(v2, v); break;
			case "<=": v = gte(v2, v); break;
			default: assert(0, "bad bin op " ~ pt.children[i+1].matches[0]);
		}
		i += 2;
	}
	return v;
}

void compileFunDef(Writer w, ParseTree fdef, Scope parentScope) {
	enforce(fdef.name=="Program.FunDef");
	string fn = fdef.children[0].matches[0];
	ArgDef[] argdefs = compileArgs(fdef.children[1]);
	w.defun(fn, argdefs, (w, as) { 
		auto scp = new Scope(argdefs, as, parentScope);
		foreach(ch; fdef.children[2..$]) 
			if (ch.name=="Program.FunDef") {
				compileFunDef(w, ch, scp);
			} else
			if (ch.name=="Program.Expr") {			
					auto v = compileExpr(w, ch, scp);
					v.gen(w);
			} else assert(0, "something weird inside FunDef");
	});
}

auto compile(Writer w, ParseTree pt) {
	auto topdefs = pt.children[0].children;
	foreach(def; topdefs) 
		if (def.name=="Program.TypeDef") {
			enforce(def.children[0].name == "Program.Name");
			types[ def.children[0].matches[0] ] = compileTypeDef(def.children[1]);
		} else
		if (def.name=="Program.FunDef") {
			compileFunDef(w, def, null);
		}
	//writeln(types);
}

void main(string[] argv)
{
	string fname = argv.length > 1 ? argv[1] : "prg.lam";
	string text = readText(fname);
	writeln(text);
	ParseTree pt = Program(text);
	writeln(pt);
	if (pt.successful) {
		Writer w = new Writer;   

		Writer wboot = new Writer;
		num(0).gen(wboot);
		wboot.put(CMD(Op.LDF, 0,0, "step"));
		wboot.put(CMD(Op.CONS));
		wboot.put(CMD(Op.RTN));
		w.addToDefs(wboot);

		compile(w, pt);
		w.finish(0);
	}

	return;
    /*Type Int = new TInt;
    Type Pos = new TTuple("x" in Int, "y" in Int);
    Type G = new TTuple("vit" in Int, "pos" in Pos, "dir" in Int);
    Type Map = new TList(new TList(Int));
    Type Me = new TTuple("vit" in Int, "pos" in Pos, "dir" in Int, "lives" in Int, "score" in Int);
    Type W = new TTuple("map" in Map, "me" in Me, "gs" in new TList(G), "fruit" in Int);
    auto ret = CMD(Op.RTN);
    //Args vars = new Args([tuple("x", Int), tuple("gs", cast(Type) new TList(G))]);
    //auto v = vars.gs.tl.tl.hd.pos.y;
    //v.gen(w);

    Writer w = new Writer;   

    Writer wboot = new Writer;
    num(0).gen(wboot);
    wboot.put(CMD(Op.LDF, 0,0, "step"));
    wboot.put(CMD(Op.CONS));
    wboot.put(ret);
    w.addToDefs(wboot);


    //def nth
    w.defun("nth", ["n" in Int, "xs" in new TList(Int)], (w, args) {            
        if0(args.n, 
                   args.xs.hd, 
                   call("nth", args.n - 1.num, args.xs.tl)).gen(w);
    });
    
    w.label("step");
    /*{ // show 3rd row
        auto args = new Args("curDir" in Int, "w" in W);
        w.defun("showRow", ["row" in Int], (w, as) {
            call("nth", as.row, args.w.map).gen(w);
        });
        call("showRow", 3.num).gen(w);
        w.put(ret);
    }*/

    /*{ //copy first ghost
        auto args = new Args("my" in Int, "w" in W);
        cons(num(0), args.w.gs.hd.dir).gen(w);
    } /
    
    { //walk around
        auto args = new Args("curDir" in Int, "w" in W);

        w.defun("cell", ["pos" in Pos, "map" in Map], (w,ca) {            
            auto row = call("nth", ca.pos.y, ca.map);
            call("nth", ca.pos.x, row).gen(w);
        });

        w.defun("addVec", ["a" in Pos, "b" in Pos], (w,as) {            
            cons(as.a.x + as.b.x, as.a.y + as.b.y).gen(w);
        });

        w.defun("dirVec", ["dir" in Int], (w,as) {
            auto vecs = list(cons(num(0), num(-1)), cons(num(1),num(0)), cons(num(0), num(1)), cons(num(-1),num(0)));
            call("nth", as.dir, vecs).gen(w);
        });

        w.defun("mod4", ["x" in Int], (w,as) {
            if0(gt(num(4), as.x),
                    as.x - num(4), //0
                    as.x).gen(w);  //1
        });

        /*w.let(["x" in Int], num(4), (w,as) {
            call("mod4", as.x).gen(w);
        }).gen(w);/
        //try curDir, then 0,1,2,3
        //try(dir) => neighbor cell value
        w.defun("try", ["dir" in Int], (w,as) {
            auto coord = call("addVec", args.w.me.pos, call("dirVec", as.dir));
            call("cell", coord, args.w.map).gen(w);
        });

        auto answer(Val x) { return cons(x, x); }

        

        if0(call("try", args.curDir),
              if0(call("try", call("mod4", args.curDir + 1.num)),
                  if0(call("try", call("mod4", args.curDir + 2.num)),
                        if0(call("try", call("mod4", args.curDir + 3.num)),
                              answer(num(0)),
                              answer(call("mod4", args.curDir + 3.num))),
                        answer(call("mod4", args.curDir + 2.num))),
                  answer(call("mod4", args.curDir + 1.num))),
              answer(args.curDir)).gen(w);
        w.put(ret);
    }

    w.finish(0);*/
}
