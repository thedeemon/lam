import std.stdio, std.typecons, std.conv, std.string;

enum Op {
    LD, LDC, LDF, AP, ADD, SUB, MUL, DIV, CEQ, CGT, CGTE, ATOM, CONS, CAR, CDR, SEL, JOIN, RTN, DUM, RAP, TSEL, TAP, TRAP, ST,
    Label
}

enum OpKind { 
    Nada, Num, Num2, Lab, Lab2
}

enum OpKind[Op] opKinds = [ 
    Op.LDC : OpKind.Num, 
    Op.LD : OpKind.Num2, 
    Op.ST : OpKind.Num2, 
    Op.ADD : OpKind.Nada,
    Op.SUB : OpKind.Nada,
    Op.MUL : OpKind.Nada,
    Op.DIV : OpKind.Nada,
    Op.CEQ : OpKind.Nada,
    Op.CGT : OpKind.Nada,
    Op.CGTE : OpKind.Nada,
    Op.ATOM : OpKind.Nada,
    Op.CONS : OpKind.Nada,
    Op.CAR : OpKind.Nada,
    Op.CDR : OpKind.Nada,
    Op.SEL : OpKind.Lab2,
    Op.TSEL : OpKind.Lab2,
    Op.JOIN : OpKind.Nada,
    Op.LDF : OpKind.Lab,
    Op.AP : OpKind.Num,
    Op.TAP : OpKind.Num,
    Op.TRAP : OpKind.Num,
    Op.RTN : OpKind.Nada,
    Op.DUM : OpKind.Num,
    Op.RAP : OpKind.Num,
    Op.Label : OpKind.Lab
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
                writeln(cmd.lbl, " -> ", ip);
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

Val call(string fn, Val[] vals...) {
    return new GenVal((Writer w) {
        foreach(v; vals) {
            v.gen(w);
        }
        w.put(CMD(Op.LDF, 0,0, fn));
        w.put(CMD(Op.AP, vals.length));
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
    w.addToDefs(w1);
}

Val eq(Val a, Val b) { return binOp(Op.CEQ, a,b); } // => 1 or 0
Val gt(Val a, Val b) { return binOp(Op.CGT, a,b); } // => 1 or 0
Val gte(Val a, Val b) { return binOp(Op.CGTE, a,b); } // => 1 or 0
Val not(Val a) { return num(1) - a; }

void main(string[] argv)
{
    Type Int = new TInt;
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
    } */
    
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

    w.finish(0);
}
