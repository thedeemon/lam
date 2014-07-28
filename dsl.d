module dsl;
import std.stdio, std.typecons, std.conv, std.string, std.range;

enum Op {
    LD, LDC, LDF, AP, ADD, SUB, MUL, DIV, CEQ, CGT, CGTE, ATOM, CONS, CAR, CDR, 
    SEL, JOIN, RTN, DUM, RAP, TSEL, TAP, TRAP, ST, DBUG, Label
}

enum OpKind { 
    Nada, Num, Num2, Lab, Lab2
}

enum OpKind[Op] opKinds = [ 
    Op.LDC : OpKind.Num,     Op.LD : OpKind.Num2,     Op.ST : OpKind.Num2, 
    Op.ADD : OpKind.Nada,    Op.SUB : OpKind.Nada,    Op.MUL : OpKind.Nada,
    Op.DIV : OpKind.Nada,    Op.CEQ : OpKind.Nada,    Op.CGT : OpKind.Nada,
    Op.CGTE : OpKind.Nada,   Op.ATOM : OpKind.Nada,   Op.CONS : OpKind.Nada,
    Op.CAR : OpKind.Nada,    Op.CDR : OpKind.Nada,    Op.SEL : OpKind.Lab2,
    Op.TSEL : OpKind.Lab2,   Op.JOIN : OpKind.Nada,   Op.LDF : OpKind.Lab,
    Op.AP : OpKind.Num,      Op.TAP : OpKind.Num,     Op.TRAP : OpKind.Num,
    Op.RTN : OpKind.Nada,    Op.DUM : OpKind.Num,     Op.RAP : OpKind.Num,
    Op.DBUG : OpKind.Nada,   Op.Label : OpKind.Lab
]; 

struct Cmd(T) {
    Op op;
    int n, n2;    
    T lbl, lbl2;
}

alias CMD = Cmd!string;

void show(T)(Cmd!T cmd, string comment = "") {
    write(cmd.op, " ");
    final switch(opKinds[cmd.op]) {
        case OpKind.Lab: write(cmd.lbl); break;
        case OpKind.Lab2: write(cmd.lbl, " ", cmd.lbl2); break;
        case OpKind.Num: write(cmd.n); break;
        case OpKind.Num2: write(cmd.n, " ", cmd.n2); break;
        case OpKind.Nada: write; break;
    }
    writeln(comment.strip.length==0 ? "" : " ; " ~ comment);
}

class Writer {
    CMD[] prg, defs;
    static int[string] funLevels;

    void put(CMD cmd) { 
        prg ~= cmd;
    }

    void addToDefs(Writer w) {
        defs ~= w.defs;
        defs ~= w.prg;
    }

    void finish(int start) {
        int[string] lbs;
        int ip = start;
        lbs[""] = 0;
        prg = defs ~ prg;
        foreach(cmd; prg) {
            if (cmd.op == Op.Label) {
                lbs[cmd.lbl] = ip;
                //writeln(cmd.lbl, " -> ", ip);
            } else 
                ip++;            
            //show(cmd);
        }
        string lbnames;
        int getLab(string lab) { 
            if (lab in lbs) { 
                lbnames ~= lab ~ " ";
                return lbs[lab];
            }
            writeln("err: unknown label ", lab);
            return -666;
        }
        //writeln("--------------------");
        foreach(cmd; prg) {
            if (cmd.op != Op.Label) {                
                auto c = Cmd!int(cmd.op, cmd.n, cmd.n2, getLab(cmd.lbl), getLab(cmd.lbl2));
                show(c, lbnames);
                lbnames = "";
            } else lbnames ~= cmd.lbl ~ ": ";
        }
    }

    bool looksUpward() {
        foreach(c; chain(defs, prg))
            if (c.op == Op.LD && c.n > 0)
                return true;
        return false;
    }
}

class Val {
    abstract void gen(Writer w);
    Val opDispatch(string s)() { return getMemb(s); };

    Val getMemb(string s) {
        assert(0, "no members here");
    }

    Val opBinary(string op)(Val v) {
        Op o;
        switch(op) {
            case "+": o = Op.ADD; break;
            case "-": o = Op.SUB; break;
            case "*": o = Op.MUL; break;
            case "/": o = Op.DIV; break;
            default: assert(0, "Val no has "~ op);
        }
        return new GenVal((Writer w) {
            gen(w);
            v.gen(w);
            w.put(CMD(o));
        });
    }
}

class Type {
    abstract Val create(Val parent);

    Tuple!(string, Type) opBinaryRight(string op)(string name)  if (op=="in") {        
        return tuple(name, this);
    }
}

class IntVal : Val {
    Val parent;
    this(Val par) { parent = par; }
    override void gen(Writer w) { parent.gen(w); }
}

class TInt : Type {
    override Val create(Val parent) {
        return new IntVal(parent);
    }
}

class ListVal : Val {
    Val parent;
    Type elementType;
    this(Val par, Type elType) {
        parent = par;
        elementType = elType;
    }
    override void gen(Writer w) {
        parent.gen(w);
    }

    override Val getMemb(string s) { // hd or tl
        if (s=="hd") {
            Val val = new GenVal((Writer w) {
                parent.gen(w);
                w.put(Cmd!string(Op.CAR));
            });
            return elementType.create(val);
        } 
        if (s=="tl") {
            Val val = new GenVal((Writer w) {
                parent.gen(w);
                w.put(Cmd!string(Op.CDR));
            });
            return (new TList(elementType)).create(val);
        }
        assert(0, "this is a list, use hd or tl");
    }
}

class TList : Type {
    Type of;
    this(Type ofWhat) { of = ofWhat; }
    override Val create(Val parent) {
        return new ListVal(parent, of);
    }
}

class GenVal : Val {
    void delegate(Writer w) genfun;
    this(void delegate(Writer w) f) { genfun = f; }
    override void gen(Writer w) { genfun(w); }
}

class VTuple : Val {
    Tuple!(string, Type)[] members;
    Val parent;

    this(Val par, Tuple!(string, Type)[] mems) { parent = par; members = mems; }

    override void gen(Writer w) {
        parent.gen(w);
    }

    override Val getMemb(string s) { 
        foreach(i, a; members) {
            if (a[0]==s) { 
                auto val = new GenVal((Writer w) {
                    parent.gen(w);
                    for(int k = 0; k < i; k++)
						w.put(Cmd!string(Op.CDR));
                    if (i < members.length-1) {
                        w.put(Cmd!string(Op.CAR));
                    }                    
                });
                return a[1].create(val);
            }
        }
        assert(0, "unknown arg " ~ s);
    }
}

class TTuple : Type {
    Tuple!(string, Type)[] members;
    this(Tuple!(string, Type)[] membs...) { 
        members = membs; 
    }
    override Val create(Val parent) {
        return new VTuple(parent, members);
    }
}

class ArgVal : Val {
    int pos, nesting;
    this(int mynum, int nst) { pos = mynum; nesting = nst; }
    override void gen(Writer w) {
        w.put(Cmd!string(Op.LD, nesting, pos));
    }
}

alias ArgDef = Tuple!(string, Type);

class Args {
    Tuple!(string, Type)[] args;
    int myLevel;

    static int curLevel = 0;

    this(ArgDef[] as...) { 
        args = as; 
        myLevel = curLevel;
    }

    Val opDispatch(string s)() {
        return getArg(s);
    }

	Val getArg(string s) {
		foreach(i, a; args) {
            if (a[0]==s) return a[1].create(new ArgVal(i, curLevel - myLevel));
        }
        assert(0, "unknown arg " ~ s);
	}
}

void label(Writer w, string lab) {
    w.put(Cmd!string(Op.Label, 0,0, lab));
}

string tmpLab(string s) {
    static int n = 0;
    n++;
    return s ~ "_" ~ n.to!string;
}


Val if0(Val what, Val ifzero, Val ifnonzero) {
    return new GenVal((Writer w) {
        what.gen(w);
        auto ifz = tmpLab("ifzero");
        auto ifnz = tmpLab("ifnonzero");
        w.put(CMD(Op.SEL, 0,0, ifnz, ifz));

        auto w1 = new Writer;
        w1.label(ifz);
        ifzero.gen(w1);
        w1.put(CMD(Op.JOIN));

        auto w2 = new Writer;
        w2.label(ifnz);
        ifnonzero.gen(w2);
        w2.put(CMD(Op.JOIN));

        w.addToDefs(w1);
        w.addToDefs(w2);
    });
}

Val binOp(Op op, Val a, Val b) { 
    return new GenVal((Writer w) { 
        a.gen(w);
        b.gen(w);
        w.put(CMD(op)); 
    });
}

Val num(int x) {  return new GenVal((Writer w) { w.put(CMD(Op.LDC, x)); }); }

Val cons(Val a, Val b) {    return binOp(Op.CONS, a,b); }

Val list(Val[] xs...) {
    Val v = num(0);
    foreach_reverse(x; xs)
        v = cons(x, v);
    return v;
}

auto defun(Writer w, string name, ArgDef[] argdefs, void delegate(Writer w1, Args ags) code) {
    auto w1 = new Writer;
    w1.label(name);
    Args.curLevel++;
    code(w1, new Args(argdefs));
    Args.curLevel--;
    w1.put(CMD(Op.RTN));
    auto looksUp = w1.looksUpward();
    if (looksUp)
        Writer.funLevels[name] = Args.curLevel;
    w.addToDefs(w1);
}

Val call(string fn, Val[] vals...) {
    if (fn in Writer.funLevels) {
        if (Writer.funLevels[fn] != Args.curLevel)
            assert(0, "calling " ~ fn ~ " from wrong nesting level");
    } 
    auto vs = vals.dup;
    return new GenVal((Writer w) {
        foreach(v; vs) {
            v.gen(w);
        }
        w.put(CMD(Op.LDF, 0,0, fn));
        w.put(CMD(Op.AP, vals.length));
    });    
}


Val let(Writer w,  ArgDef[] argdefs, Val what, void delegate(Writer w1, Args ags) code) {
    auto fn = tmpLab("let_in");
    w.defun(fn, argdefs, code);
    return call(fn, what);
}

Val eq(Val a, Val b) { return binOp(Op.CEQ, a,b); } // => 1 or 0
Val gt(Val a, Val b) { return binOp(Op.CGT, a,b); } // => 1 or 0
Val gte(Val a, Val b) { return binOp(Op.CGTE, a,b); } // => 1 or 0
Val not(Val a) { return num(1) - a; }
