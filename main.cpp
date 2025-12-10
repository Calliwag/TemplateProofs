    /*

    Axioms

    */

class Check;

class Axioms
{
public:
    //=====
    // A^B
    //=====
    template <typename A, typename B>
    struct And{private: And(){}; friend class Axioms; friend class Check; };

    // A^B |- B^A
    template <typename A, typename B>
    static And<B,A> And_Commute(And<A,B>) { return And<B,A>(); }

    // A^B |- A
    template <typename A, typename B>
    static A And_Extract1(And<A,B>) { return A(); }

    // A,B |- A^B
    template <typename A, typename B>
    static And<A,B> And_Construct(A,B) { return And<A,B>(); }


    //=====
    // !A
    //=====
    template <typename A>
    struct Not{private: Not(){}; friend class Axioms; friend class Check; };

    // !(!A) |- A
    template <typename A>
    static A Not_DoubleToTrue(Not<Not<A>>) { return A(); }

    // A |- !(!A)
    template <typename A>
    static Not<Not<A>> Not_TrueToDouble(A) { return Not<Not<A>>(); }


    //=====
    // AvB
    //=====
    template <typename A, typename B>
    struct Or{private: Or(){}; friend class Axioms; friend class Check;};

    // AvB |- BvA
    template <typename A, typename B>
    static Or<B,A> Or_Commute(Or<A,B>) { return Or<B,A>(); };

    // A |- AvB
    template <typename A, typename B>
    static Or<A,B> Or_Construct(A) { return Or<A,B>(); };

    // AvB,!B |- A
    template <typename A, typename B>
    static A Or_Extract1(Or<A,B>,Not<B>) { return A(); };

    // AvA |- A
    template <typename A>
    static A Or_Extract(Or<A,A>) { return A(); };


    //======
    // A=>B
    //======
    template <typename A, typename B>
    using Imply = Or<Not<A>,B>;
};


/*

Theorems

*/

// A^B |- B
template <typename A, typename B>
static B And_Extract_2(Axioms::And<A,B> ab)
{
    return Axioms::And_Extract1(Axioms::And_Commute(ab));
}

// A=>!A |- !A
template <typename A>
static Axioms::Not<A> Contradiction(Axioms::Imply<A,Axioms::Not<A>> imp)
{
    return Axioms::Or_Extract(imp);
}

// A=>B,A |- B
template <typename A, typename B>
static B ModusPonens(Axioms::Imply<A,B> imp,A a)
{
    return Axioms::Or_Extract1(Axioms::Or_Commute(imp),Axioms::Not_TrueToDouble(a));
}


/*

Theorem Checker

*/

class Check
{
    struct I1 {};
    struct I2 {};

    void check ()
    {
        And_Extract_2<I1,I2>(Axioms::And<I1,I2>());
        Contradiction(Axioms::Imply<I1,Axioms::Not<I1>>());
        ModusPonens(Axioms::Imply<I1,I2>(),I1());
    }
};

int main()
{
    return 0;
}
