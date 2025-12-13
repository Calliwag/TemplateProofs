#include <concepts>

class Check;
class Axioms;

class PropBase {};

template <typename T>
concept Prop = std::derived_from<T, PropBase>;


/*
====================================
            Definitions
====================================
*/

//
// A=>B
//
template<Prop A, Prop B>
struct I : public PropBase {private: I(){}; friend class Axioms; friend class Check;};

//
// ¬A
//
template<Prop A>
struct N : public PropBase {private: N(){}; friend class Axioms; friend class Check;};


/*
============================================
        Derived Logical Connectives
============================================
*/

//
// A∨B
//
template<Prop A, Prop B>
using Or = I<N<A>,B>;

//
// A∧B
//
template<Prop A, Prop B>
using And = N<Or<N<A>,N<B>>>;


// Source of axioms: https://www.maths.tcd.ie/~odunlain/u11602/online_notes/pdf_propos.pdf
class Axioms
{  
public:

/*
=======================================
                Axioms
=======================================
*/

    //
    // A => (B => A)
    //
    template<Prop A, Prop B>
    static I<A,I<B,A>> Axiom1() { return I<A,I<B,A>>(); };

    //
    // (A => (B=>C)) => ((A=>B) => (B=>C))
    //
    template<Prop A, Prop B, Prop C>
    static I<I<A,I<B,C>>,I<I<A,B>,I<A,C>>> Axiom2() { return I<I<A,I<B,C>>,I<I<A,B>,I<A,C>>>(); };

    //
    // (¬B=>¬A) => ((¬B=>A) => B)
    //
    template<Prop A, Prop B>
    static I<I<N<B>,N<A>>,I<I<N<B>,A>,B>> Axiom3() { return I<I<N<B>,N<A>>,I<I<N<B>,A>,B>>(); }

/*
========================================
            Deduction Rules
========================================
*/

    //
    // Modus Ponens: A=>B,A |- B
    //
    template<Prop A, Prop B>
    static B MP(I<A,B>,A) { return B(); };

    //
    // Deduction Theorem: If Logic,A |- B, then Logic |- A=>B
    //
    template<Prop A, Prop B>
    static I<A,B> (*DT(B(*)(A)))()
    {
        return [](){ return I<A,B>(); };
    };

    //
    // Deduction Theorem (2): If Logic,A,P1 |- B, then Logic,P1 |- A=>B
    //
    template<Prop A, Prop E1, Prop B>
    static I<A,B> (*DT2(B(*)(A,E1)))(E1)
    {
        return [](E1){ return I<A,B>(); };
    };

    //
    // Deduction Theorem (3): If Logic,A,P1,P2 |- B, then Logic,P1,P2 |- A=>B
    //
    template<Prop A, Prop E1, Prop E2, Prop B>
    static I<A,B> (*DT3(B(*)(A,E1,E2)))(E1,E2)
    {
        return [](E1,E2){ return I<A,B>(); };
    };

    // Generally, for n ∈ ℕ:
    // Deduction Theorem (n): If Logic,A,P1,P2,...,Pn |- B, then Logic,P1,P2,...,Pn |- A=>B
};


/*
=================================
            Theorems
=================================
*/

// Logic |- A=>A
template<Prop A>
I<A,A> ImpSelf()
{
    auto step1 = Axioms::Axiom2<A,I<A,A>,A>();
    auto step2 = Axioms::Axiom1<A,I<A,A>>();
    auto step3 = Axioms::MP(step1,step2);
    auto step4 = Axioms::Axiom1<A,A>();
    auto step5 = Axioms::MP(step3,step4);
    return step5;
}

// Logic + ¬A=>A |- A
template<Prop A>
A Contradict(I<N<A>,A> imp)
{
    auto step1 = ImpSelf<N<A>>();
    auto step2 = Axioms::Axiom3<A,A>();
    auto step3 = Axioms::MP(step2,step1);
    auto step4 = Axioms::MP(step3,imp);
    return step4;
}

// Logic + ¬¬A |- A
template<Prop A>
A DoubleNot(N<N<A>> nna)
{
    auto step1 = Axioms::MP(Axioms::Axiom1<N<N<A>>,N<A>>(),nna);
    auto step2 = ImpSelf<N<A>>();
    auto step3 = Axioms::Axiom3<N<A>,A>();
    auto step4 = Axioms::MP(step3,step1);
    auto step5 = Axioms::MP(step4,step2);
    return step5;
}

// Logic + A, A=>B, B=>C |- C
template<Prop A, Prop B, Prop C>
C ImpTransit_(A a, I<A,B> ab, I<B,C> bc)
{
    auto step1 = Axioms::MP(ab,a);
    auto step2 = Axioms::MP(bc,step1);
    return step2;
}

// Logic + A=>B, B=>C |- A=>C
template<Prop A, Prop B, Prop C>
I<A,C> ImpTransit(I<A,B> ab, I<B,C> bc)
{
    return Axioms::DT3(ImpTransit_<A,B,C>)(ab,bc);
}

// Logic + ¬B, A=>B |- ¬A
template<Prop A, Prop B>
N<A> ContraPositive_(N<B> nb, I<A,B> ab)
{
    auto step1 = Axioms::DT(DoubleNot<A>)();
    auto step2 = ImpTransit(step1,ab);
    auto step3 = Axioms::MP(Axioms::Axiom1<N<B>,N<N<A>>>(),nb);
    auto step4 = Axioms::MP(Axioms::Axiom3<B,N<A>>(),step3);
    auto step5 = Axioms::MP(step4,step2);
    return step5;
}

// Logic + A=>B |- (¬B)=>(¬A)
template<Prop A, Prop B>
I<N<B>,N<A>> ContraPositive(I<A,B> ab)
{
    return Axioms::DT2(ContraPositive_<A,B>)(ab);
}

// Logic + A |- ¬¬A
template<Prop A>
N<N<A>> DoubleNotRev(A a)
{
    auto step1 = Axioms::MP(Axioms::Axiom1<A,N<A>>(),a);
    auto step2 = ContraPositive(ContraPositive(step1));
    auto step3 = Contradict(step2);
    return step3;
}

// Logic + B |- A∨B
template<Prop A, Prop B>
Or<A,B> OrConstruct2(B b)
{
    auto step1 = Axioms::Axiom1<B,N<A>>();
    auto step2 = Axioms::MP(step1,b);
    return step2;
}

// Logic + A∨B |- B∨A
template<Prop A, Prop B>
Or<B,A> OrCommute(Or<A,B> ab)
{
    auto step1 = ContraPositive(ab);
    auto step2 = ImpTransit(step1,Axioms::DT(DoubleNot<A>)());
    return step2;
}

// Logic + A |- A∨B
template<Prop A, Prop B>
Or<A,B> OrConstruct1(A a)
{
    return OrCommute(OrConstruct2<B,A>(a));
}

// Logic + A∧B |- A
template<Prop A, Prop B>
A AndExtract1(And<A,B> ab)
{
    auto step1 = Axioms::DT(OrConstruct1<N<A>,N<B>>)();
    auto step2 = ContraPositive(step1);
    auto step3 = Axioms::DT(DoubleNot<A>)();
    auto step4 = ImpTransit(step2,step3);
    auto step5 = Axioms::MP(step4,ab);
    return step5;
}

// Logic + A∧B |- B
template<Prop A, Prop B>
B AndExtract2(And<A,B> ab)
{
    auto step1 = Axioms::DT(OrConstruct2<N<A>,N<B>>)();
    auto step2 = ContraPositive(step1);
    auto step3 = Axioms::DT(DoubleNot<B>)();
    auto step4 = ImpTransit(step2,step3);
    auto step5 = Axioms::MP(step4,ab);
    return step5;
}

// Logic + A, B |- A∧B
template<Prop A, Prop B>
And<A,B> AndConstruct(A a, B b)
{
    auto step1 = +[](I<N<N<A>>,N<B>> X, A a, B b)
    {
        auto step1_1 = +[](I<N<N<A>>,N<B>> X, A a, B b)
        {
            auto step1_1_1 = DoubleNotRev(a);
            auto step1_1_2 = Axioms::MP(X,step1_1_1);
            return step1_1_2;
        };
        auto step1_2 = Axioms::DT3(step1_1)(a,b);
        auto step1_3 = ContraPositive(step1_2);
        auto step1_4 = DoubleNotRev(b);
        auto step1_5 = Axioms::MP(step1_3,step1_4);
        return step1_5;
    };
    auto step2 = Axioms::DT3(step1)(a,b);
    auto step3 = ContraPositive(step2);
    auto step4 = Contradict(step3);
    return step4;
}


/*
======================================
            Proof Checker
======================================
*/

struct P1 : public PropBase {private: P1(){}; friend class Axioms; friend class Check;};
struct P2 : public PropBase {private: P2(){}; friend class Axioms; friend class Check;};
struct P3 : public PropBase {private: P3(){}; friend class Axioms; friend class Check;};
struct P4 : public PropBase {private: P4(){}; friend class Axioms; friend class Check;};

class Check
{
public:
    static void check ()
    {
        ImpSelf<P1>();

        Contradict(I<N<P1>,P1>());

        DoubleNot(N<N<P1>>());

        ImpTransit_(P1(), I<P1,P2>(), I<P2,P3>());
        ImpTransit(I<P1,P2>(),I<P2,P3>());

        ContraPositive_(N<P2>(),I<P1,P2>());
        ContraPositive(I<P1,P2>());

        DoubleNotRev<P1>(P1());

        OrConstruct2<P1,P2>(P2());
        OrCommute(Or<P1,P2>());
        OrConstruct1<P1,P2>(P1());

        AndExtract1(And<P1,P2>());
        AndExtract2(And<P1,P2>());

        AndConstruct(P1(),P2());
    }
};

int main()
{
    Check::check();
    return 0;
}
