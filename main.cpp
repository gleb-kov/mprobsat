#include "bit_vector.h"

#include <cmath>
#include <iostream>
#include <fstream>
#include <stdexcept>
#include <vector>
#include <limits>
#include <random>
#include <cstring>

/*
 * https://www.uni-ulm.de/fileadmin/website_uni_ulm/iui.inst.190/Mitarbeiter/balint/SAT2012.pdf
 */

constexpr size_t MAX_CLAUSE_LENGTH = 10; //maximum number of literals per clause; 10 is enough for reimage problems
constexpr size_t STOREBLOCK = 20000;
constexpr int64_t maxTries = std::numeric_limits<int64_t>::max();
constexpr int64_t maxFlips = std::numeric_limits<int64_t>::max();
constexpr bool use_poly_func = true; // exp otherwise
constexpr double eps = 1.0;
constexpr int64_t seed = 1638826429;

/*--------*/

/*----Instance data (independent from assignment)----*/
size_t numVars;
size_t numClauses;
size_t numLiterals;

/** The value of the variables. The numbering starts at 1 and the possible values are 0 or 1. */
TBitVector litValue;
/** The clauses of the formula represented as: clause[clause_number][literal_number].
 * The clause and literal numbering start both at 1. literal and clause 0 0 is sentinel*/
int **clause;
/**min and max clause length*/
size_t maxClauseSize;
/** The number of occurrence of each literal.*/
size_t *numOccurrence;
/** The clauses where each literal occurs. For literal i : occurrence[i+MAXATOMS][j] gives the clause =
 * the j'th occurrence of literal i.  */
size_t **occurrence;
size_t maxNumOccurences = 0; //maximum number of occurences for a literal
/*--------*/

/**----Assignment dependent data----*/
/** The number of false clauses.*/
size_t numFalse;
size_t bestNumFalse;
/** Array containing all clauses that are false. Managed as a list.*/
size_t *falseClause;
/** whereFalse[i]=j tells that clause i is listed in falseClause at position j.  */
size_t *whereFalse;
/** The number of true literals in each clause. */
size_t *numTrueLit;
/*the number of clauses the variable i will make unsat if flipped*/
int *breaks;
/** critVar[i]=j tells that for clause i the variable j is critically responsible for satisfying i.*/
int *critVar;

/*----probSAT variables----*/
/** Look-up table for the functions. The values are computed in the initProbSAT method.*/
std::vector<double> probsBreak;
/** contains the probabilities of the variables from an unsatisfied clause*/
double *probs;

/** Run time variables variables*/
int64_t flip;

/////////////////////////////

auto& Random_engine() {
    static std::random_device rd;
    static std::mt19937 eng(seed);
    // static std::default_random_engine eng(rd());
    return eng;
}

float RandFrac() {
    static std::uniform_real_distribution<float> distr(0.0, 1.0);
    static auto& eng = Random_engine();
    return distr(eng);
}

void PrintSolution() {
    std::ofstream fout("result.txt");
    for (size_t i = 1; i <= numVars; ++i) {
        if (!litValue.Test(i)) {
            fout << '-';
        }
        fout << i << ' ';
    }
}

void AllocateMemory() {
    // Allocating memory for the instance data (independent from the assignment).
    numLiterals = numVars * 2;
    litValue.Resize(numVars + 1);
    clause = (int **) malloc(sizeof(int *) * (numClauses + 1));
    numOccurrence = (size_t *) malloc(sizeof(size_t) * (numLiterals + 1));
    occurrence = (size_t **) malloc(sizeof(size_t *) * (numLiterals + 1));
    critVar = (int *) malloc(sizeof(int) * (numClauses + 1));

    // Allocating memory for the assignment dependent data.
    falseClause = (size_t *) malloc(sizeof(size_t) * (numClauses + 1));
    whereFalse = (size_t *) malloc(sizeof(size_t) * (numClauses + 1));
    numTrueLit = (size_t *) malloc(sizeof(size_t) * (numClauses + 1));

    probs = (double *) malloc(sizeof(double) * (numVars + 1));
    breaks = (int *) malloc(sizeof(int) * (numVars + 1));
}

void ParseFile(const char* fileName) {
    FILE *fp = fopen(fileName, "r");

    for (;;) {
        char c;
        c = fgetc(fp);
        if (c == 'c') //comment line - skip content
            do {
                c = fgetc(fp); //read the complete comment line until a eol is detected.
            } while ((c != '\n') && (c != EOF));
        else if (c == 'p') { //p-line detected
            if ((fscanf(fp, "%*s %zu %zu", &numVars, &numClauses))) //%*s should match with "cnf"
                break;
        }
    }

    AllocateMemory();
    std::memset(numOccurrence, 0, numLiterals + 1);
    size_t *numOccurrenceT = (size_t *) malloc(sizeof(size_t) * (numLiterals + 1));
    std::memset(numOccurrenceT, 0, numLiterals + 1);

    maxClauseSize = 0;
    size_t freeStore = 0;
    int *tempClause = nullptr;

    for (size_t i = 1; i <= numClauses; ++i) {
        if (freeStore < MAX_CLAUSE_LENGTH) {
            tempClause = (int *) malloc(sizeof(int) * STOREBLOCK);
            freeStore = STOREBLOCK;
        }
        clause[i] = tempClause;
        size_t clauseSize = 0;
        int lit;
        do {
            fscanf(fp, "%i", &lit);
            if (lit != 0) {
                ++clauseSize;
                *tempClause++ = lit;
                ++numOccurrenceT[numVars + lit];
            } else {
                *tempClause++ = 0; //0 sentinel as literal!
            }
            --freeStore;
        } while (lit != 0);

        maxClauseSize = std::max(maxClauseSize, clauseSize);
    }

    for (size_t i = 0; i < numLiterals + 1; ++i) {
        occurrence[i] = (size_t *) malloc(sizeof(size_t) * (numOccurrenceT[i] + 1));
        maxNumOccurences = std::max(maxNumOccurences, numOccurrenceT[i]);
    }

    for (size_t i = 1; i <= numClauses; ++i) {
        size_t j = 0;
        int lit;
        while ((lit = clause[i][j])) {
            occurrence[lit + numVars][numOccurrence[lit + numVars]++] = i;
            ++j;
        }
        occurrence[lit + numVars][numOccurrence[lit + numVars]] = 0; //sentinel at the end!
    }

    free(numOccurrenceT);
    fclose(fp);
}

void InitSatInfo() {
    int critLit = 0, lit;
    numFalse = 0;

    std::memset(numTrueLit, 0, numClauses + 1);
    std::memset(whereFalse, 0, numClauses + 1);
    std::memset(breaks, 0, numVars + 1);

    //pass trough all clauses and apply the assignment previously generated
    for (size_t i = 1; i <= numClauses; ++i) {
        size_t j = 0;
        while ((lit = clause[i][j])) {
            if (litValue.Test(std::abs(lit)) == (lit > 0)) {
                ++numTrueLit[i];
                critLit = lit;
            }
            ++j;
        }
        if (numTrueLit[i] == 1) {
            //if the clause has only one literal that causes it to be sat,
            //then this var. will break the sat of the clause if flipped.
            critVar[i] = std::abs(critLit);
            ++breaks[std::abs(critLit)];
        } else if (numTrueLit[i] == 0) {
            //add this clause to the list of unsat caluses.
            falseClause[numFalse] = i;
            whereFalse[i] = numFalse;
            ++numFalse;
        }
    }
}

void CheckAssignment() {
    for (size_t i = 1; i <= numClauses; ++i) {
        bool satisf = false;
        size_t j = 0;
        int lit;
        while ((lit = clause[i][j])) {
            if (litValue.Test(std::abs(lit)) == (lit > 0)) {
                satisf = true;
            }
            ++j;
        }
        if (!satisf) {
            throw std::runtime_error("the assignment is not valid!");
        }
    }
}

void PickAndFlip() {
    size_t tClause;
    size_t rClause = falseClause[flip % numFalse];
    double sumProb = 0;
    int i = 0;
    int var;

    while ((var = std::abs(clause[rClause][i]))) {
        probs[i] = probsBreak[breaks[var]];
        sumProb += probs[i];
        ++i;
    }

    double randPosition = RandFrac() * sumProb;
    for (i = i - 1; i != 0; --i) {
        sumProb -= probs[i];
        if (sumProb <= randPosition)
            break;
    }

    int bestVar = std::abs(clause[rClause][i]);
    //if x=1 then all clauses containing -x will be made sat after fliping x
    //if x=0 then all clauses containing x will be made sat after fliping x
    //tells which literal of x will make the clauses where it appears sat.
    int xMakesSat = litValue.Test(bestVar) ? -bestVar : bestVar;
    litValue.Revert(bestVar);

    //1. all clauses that contain the literal xMakesSat will become SAT, if they where not already sat.
    i = 0;
    while ((tClause = occurrence[xMakesSat + numVars][i])) {
        //if the clause is unsat it will become SAT so it has to be removed from the list of unsat-clauses.
        if (numTrueLit[tClause] == 0) {
            //remove from unsat-list
            falseClause[whereFalse[tClause]] = falseClause[--numFalse]; //overwrite this clause with the last clause in the list.
            whereFalse[falseClause[numFalse]] = whereFalse[tClause];
            whereFalse[tClause] = -1;
            critVar[tClause] = std::abs(xMakesSat); //this variable is now critically responsible for satisfying tClause
            //adapt the scores of the variables
            //the score of x has to be decreased by one because x is critical and will break this clause if fliped.
            ++breaks[bestVar];
        } else {
            //if the clause is satisfied by only one literal then the score has to be increased by one for this var.
            //because fliping this variable will no longer break the clause
            if (numTrueLit[tClause] == 1) {
                --breaks[critVar[tClause]];
            }
        }
        //if the number of numTrueLit[tClause]>=2 then nothing will change in the scores
        ++numTrueLit[tClause]; //the number of true Lit is increased.
        ++i;
    }
    //2. all clauses that contain the literal -xMakesSat=0 will not be longer satisfied by variable x.
    //all this clauses contained x as a satisfying literal
    i = 0;
    while ((tClause = occurrence[numVars - xMakesSat][i])) {
        if (numTrueLit[tClause] == 1) { //then xMakesSat=1 was the satisfying literal.
            //this clause gets unsat.
            falseClause[numFalse] = tClause;
            whereFalse[tClause] = numFalse;
            ++numFalse;
            //the score of x has to be increased by one because it is not breaking any more for this clause.
            --breaks[bestVar];
            //the scores of all variables have to be increased by one ; inclusive x because flipping them will make the clause again sat
        } else if (numTrueLit[tClause] == 2) { //find which literal is true and make it critical and decrease its score
            size_t j = 0;
            while ((var = std::abs(clause[tClause][j]))) {
                if (((clause[tClause][j] > 0) ==
                     litValue.Test(std::abs(var)))) { //x can not be the var anymore because it was flipped //&&(xMakesSat!=var)
                    critVar[tClause] = var;
                    ++breaks[var];
                    break;
                }
                ++j;
            }
        }
        --numTrueLit[tClause];
        ++i;
    }

}

void SetupParameters() {
    double cb = 5.4;

    if (maxClauseSize <= 3) {
        cb = 2.06;
    } else if (maxClauseSize <= 4) {
        cb = 2.85;
    } else if (maxClauseSize <= 5) {
        cb = 3.7;
    } else if (maxClauseSize <= 6) {
        cb = 5.1;
    }

    probsBreak.resize(maxNumOccurences + 1);
    if (use_poly_func) {
        for (size_t i = 0; i <= maxNumOccurences; ++i) {
            probsBreak[i] = pow((eps + i), -cb);
        }
    } else {
        for (int i = 0; i <= maxNumOccurences; ++i) {
            probsBreak[i] = pow(cb, -i);
        }
    }
}

int main(int argc, char *argv[]) {
    srand(seed);
    ParseFile(*(argv + 1));
    SetupParameters();

    for (int64_t iter = 0; iter < maxTries; ++iter) {
        litValue.FillRandom(Random_engine());

        InitSatInfo();
        bestNumFalse = numClauses;

        for (flip = 0; flip < maxFlips; ++flip) {
            if (numFalse == 0)
                break;

            PickAndFlip();

            if (numFalse < bestNumFalse) {
                std::cout << flip << ' ' << numFalse << std::endl;
                bestNumFalse = numFalse;
            }
        }

        if (numFalse == 0) {
            CheckAssignment();
            std::cout << "SATISFIABLE\n";
            PrintSolution();
            break;
        } else {
            std::cout << "UNKNOWN best=" << bestNumFalse << '\n';
        }
    }

    std::cout << "numFlips: " << flip
              << ", avg. flips/variable: " << (double) flip / (double) numVars
              << ", avg. flips/clause: " << (double) flip / (double) numClauses
              << std::endl;
    return 0;
}