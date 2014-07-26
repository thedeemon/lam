import std.stdio, std.typecons, std.conv;

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

void show(T)(Cmd!T cmd) {
    write(cmd.op, " ");
    final switch(opKinds[cmd.op]) {
        case OpKind.Lab: writeln(cmd.lbl); break;
        case OpKind.Lab2: writeln(cmd.lbl, " ", cmd.lbl2); break;
        case OpKind.Num: writeln(cmd.n); break;
        case OpKind.Num2: writeln(cmd.n, " ", cmd.n2); break;
        case OpKind.Nada: writeln; break;
    }
}

class Writer {
    Cmd!string[] prg;
    
    void put(Cmd!string cmd) { 
        prg ~= cmd;
    }

    void finish(int start) {
        int[string] lbs;
        int ip = start;
        lbs[""] = 0;
        foreach(cmd; prg) {
            if (cmd.op == Op.Label) {
                lbs[cmd.lbl] = ip;
                writeln(cmd.lbl, " -> ", ip);
            } else 
                ip++;            
        }
        foreach(cmd; prg) {
            if (cmd.op != Op.Label) {
                auto c = Cmd!int(cmd.op, cmd.n, cmd.n2, lbs[cmd.lbl], lbs[cmd.lbl2]);
                show(c);
            }
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
    this(Ts...)(Ts membs) { 
        foreach(m; membs)
            members ~= m; 
    }
    override Val create(Val parent) {
        return new VTuple(parent, members);
    }
}

class ArgVal : Val {
    int pos;
    this(int mynum) { pos = mynum; }
    override void gen(Writer w) {
        w.put(Cmd!string(Op.LD, 0, pos));
    }
}

class Args {
    Tuple!(string, Type)[] args;
    this(Ts...)(Ts as) { 
        foreach(a; as)
            args ~= a; 
    }

    Val opDispatch(string s)() {
        foreach(i, a; args) {
            if (a[0]==s) return a[1].create(new ArgVal(i));
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
    return s ~ n.to!string;
}


void if0(Writer w, Val what, Val ifzero, Val ifnonzero, Cmd!string end) {
    what.gen(w);
    auto ifz = tmpLab("ifzero");
    auto ifnz = tmpLab("ifnonzero");
    w.put(CMD(Op.TSEL, 0,0, ifnz, ifz));
    w.label(ifz);
    ifzero.gen(w);
    w.put(end);
    w.label(ifnz);
    ifnonzero.gen(w);
    w.put(end);
}

Val call(V...)(string fn, V vals) {
    return new GenVal((Writer w) {
        foreach(v; vals) {
            v.gen(w);
        }
        w.put(CMD(Op.LDF, 0,0, fn));
        w.put(CMD(Op.AP, vals.length));
    });    
}

Val num(int x) {
    return new GenVal((Writer w) { w.put(CMD(Op.LDC, x)); });
}

Val cons(Val a, Val b) {
    return new GenVal((Writer w) { 
        a.gen(w);
        b.gen(w);
        w.put(CMD(Op.CONS)); 
    });
}

void main(string[] argv)
{
    Type Int = new TInt;
    Type Pos = new TTuple("x" in Int, "y" in Int);
    Type G = new TTuple("vit" in Int, "pos" in Pos, "dir" in Int);
    Writer w = new Writer;   
    Type Map = new TList(new TList(Int));
    Type Me = new TTuple("vit" in Int, "pos" in Pos, "dir" in Int, "lives" in Int, "score" in Int);
    Type W = new TTuple("map" in Map, "me" in Me, "gs" in new TList(G), "fruit" in Int);

    //Args vars = new Args([tuple("x", Int), tuple("gs", cast(Type) new TList(G))]);
    //auto v = vars.gs.tl.tl.hd.pos.y;
    //v.gen(w);

    //def nth
    /*w.label("nth");
    auto args = new Args("n" in Int, "xs" in new TList(Int));
    w.if0(args.n, 
            args.xs.hd, 
            call("nth", args.n - num(1), args.xs.tl), 
          CMD(Op.RTN));*/

    //copy first ghost
    w.label("step");
    auto args = new Args("my" in Int, "w" in W);
    cons(num(0), args.w.gs.hd.dir).gen(w);


    

    w.finish(4);
}
