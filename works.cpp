#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <unistd.h>
#include <sys/times.h>
#include <string.h>
#include <getopt.h>
#include <fstream>
#include <vector>
#include <algorithm>
#include <random>

#define MAXCLAUSELENGTH 10000 //maximum number of literals per clause //TODO: eliminate this limit
#define STOREBLOCK  20000
# undef LLONG_MAX
#define LLONG_MAX  9223372036854775807
#define BIGINT long long int

void (*initLookUpTable)() = NULL;
void (*pickAndFlipVar)() = NULL;

/*--------*/

/*----Instance data (independent from assignment)----*/
/** The numbers of variables. */
int numVars;
/** The number of clauses. */
int numClauses;
/** The number of literals. */
int numLiterals;
/** The value of the variables. The numbering starts at 1 and the possible values are 0 or 1. */
std::vector<char> atom;
/** The clauses of the formula represented as: clause[clause_number][literal_number].
 * The clause and literal numbering start both at 1. literal and clause 0 0 is sentinel*/
int **clause;
/**min and max clause length*/
int maxClauseSize;
int minClauseSize;
/** The number of occurrence of each literal.*/
int *numOccurrence;
/** The clauses where each literal occurs. For literal i : occurrence[i+MAXATOMS][j] gives the clause =
 * the j'th occurrence of literal i.  */
int **occurrence;
int maxNumOccurences = 0; //maximum number of occurences for a literal
/*--------*/

/**----Assignment dependent data----*/
/** The number of false clauses.*/
int numFalse;
/** Array containing all clauses that are false. Managed as a list.*/
int *falseClause;
/** whereFalse[i]=j tells that clause i is listed in falseClause at position j.  */
int *whereFalse;
/** The number of true literals in each clause. */
unsigned short *numTrueLit;
/*the number of clauses the variable i will make unsat if flipped*/
int *breaks;
/** critVar[i]=j tells that for clause i the variable j is critically responsible for satisfying i.*/
int *critVar;
int bestVar;

/*----probSAT variables----*/
/** Look-up table for the functions. The values are computed in the initProbSAT method.*/
double *probsBreak;
/** contains the probabilities of the variables from an unsatisfied clause*/
double *probs;
double cb; //for break
double eps = 1.0;
int fct = 0; //function to use 0= poly 1=exp
int caching = 0;
/*--------*/

/*----Input file variables----*/
FILE *fp;
char *fileName;
/*---------*/

/** Run time variables variables*/BIGINT seed;
BIGINT maxTries = LLONG_MAX;
BIGINT maxFlips = 20000;
BIGINT flip;
int bestNumFalse;
//parameters flags - indicates if the parameters were set on the command line
int cb_spec = 0, fct_spec = 0, caching_spec = 0;

inline int abs(int a) {
    return (a < 0) ? -a : a;
}

void printFormulaProperties() {
    printf("\nc %-20s:  %s\n", "instance name", fileName);
    printf("c %-20s:  %d\n", "number of variables", numVars);
    printf("c %-20s:  %d\n", "number of literals", numLiterals);
    printf("c %-20s:  %d\n", "number of clauses", numClauses);
    printf("c %-20s:  %d\n", "max. clause length", maxClauseSize);
}

void printSolverParameters() {
    printf("\nc probSAT parameteres: \n");
    printf("c %-20s: %-20s\n", "using:", "only break");
    if (fct == 0)
        printf("c %-20s: %-20s\n", "using:", "polynomial function");
    else
        printf("c %-20s: %-20s\n", "using:", "exponential function");

    printf("c %-20s: %6.6f\n", "cb", cb);
    if (fct == 0) { //poly
        printf("c %-20s: %-20s\n", "function:", "probsBreak[break]*probsMake[make] = pow((eps + break), -cb);");
        printf("c %-20s: %6.6f\n", "eps", eps);
    } else { //exp
        printf("c %-20s: %-20s\n", "function:", "probsBreak[break]*probsMake[make] = pow(cb, -break);");
    }
    if (caching)
        printf("c %-20s: %-20s\n", "using:", "caching of break values");
    else
        printf("c %-20s: %-20s\n", "using:", "no caching of break values");
    //printProbs();
    printf("\nc general parameteres: \n");
    printf("c %-20s: %lli\n", "maxTries", maxTries);
    printf("c %-20s: %lli\n", "maxFlips", maxFlips);
    printf("c %-20s: %lli\n", "seed", seed);
    printf("c %-20s: \n", "-->Starting solver");
    fflush(stdout);
}

void printSolution() {
    std::ofstream fout("result.txt");
    for (size_t i = 1; i <= numVars; ++i) {
        if (!atom[i]) {
            fout << '-';
        }
        fout << i << std::endl;
    }
}

static inline void allocateMemory() {
    // Allocating memory for the instance data (independent from the assignment).
    numLiterals = numVars * 2;
    atom.resize(numVars + 1);
    clause = (int**) malloc(sizeof(int*) * (numClauses + 1));
    numOccurrence = (int*) malloc(sizeof(int) * (numLiterals + 1));
    occurrence = (int**) malloc(sizeof(int*) * (numLiterals + 1));
    critVar = (int*) malloc(sizeof(int) * (numClauses + 1));

    // Allocating memory for the assignment dependent data.
    falseClause = (int*) malloc(sizeof(int) * (numClauses + 1));
    whereFalse = (int*) malloc(sizeof(int) * (numClauses + 1));
    numTrueLit = (unsigned short*) malloc(sizeof(unsigned short) * (numClauses + 1));
}

static inline void parseFile() {
    int i, j;
    int lit, r;
    int clauseSize;
    int tatom;
    char c;
    long filePos;
    fp = NULL;
    fp = fopen(fileName, "r");
    if (fp == NULL) {
        fprintf(stderr, "c Error: Not able to open the file: %s\n", fileName);
        exit(-1);
    }

    // Start scanning the header and set numVars and numClauses
    for (;;) {
        c = fgetc(fp);
        if (c == 'c') //comment line - skip content
            do {
                c = fgetc(fp); //read the complete comment line until a eol is detected.
            } while ((c != '\n') && (c != EOF));
        else if (c == 'p') { //p-line detected
            if ((fscanf(fp, "%*s %d %d", &numVars, &numClauses))) //%*s should match with "cnf"
                break;
        } else {
            printf("c No parameter line found! Computing number of atoms and number of clauses from file!\n");
            r = fseek(fp, -1L, SEEK_CUR); //try to unget c
            if (r == -1) {
                fprintf(stderr, "c Error: Not able to seek in file: %s", fileName);
                exit(-1);
            }
            filePos = ftell(fp);
            if (r == -1) {
                fprintf(stderr, "c Error: Not able to obtain position in file: %s", fileName);
                exit(-1);
            }

            numVars = 0;
            numClauses = 0;
            for (; fscanf(fp, "%i", &lit) == 1;) {
                if (lit == 0)
                    numClauses++;
                else {
                    tatom = abs(lit);
                    if (tatom > numVars)
                        numVars = tatom;
                }
            }
            printf("c numVars: %d numClauses: %d\n", numVars, numClauses);

            r = fseek(fp, filePos, SEEK_SET); //try to rewind the file to the beginning of the formula
            if (r == -1) {
                fprintf(stderr, "c Error: Not able to seek in file: %s", fileName);
                exit(-1);
            }

            break;
        }
    }
    // Finished scanning header.
    //allocating memory to use!
    allocateMemory();
    maxClauseSize = 0;
    minClauseSize = MAXCLAUSELENGTH;
    int *numOccurrenceT = (int*) malloc(sizeof(int) * (numLiterals + 1));

    int freeStore = 0;
    int *tempClause = 0;
    for (i = 0; i < numLiterals + 1; i++) {
        numOccurrence[i] = 0;
        numOccurrenceT[i] = 0;
    }

    for (i = 1; i <= numClauses; i++) {
        whereFalse[i] = -1;
        if (freeStore < MAXCLAUSELENGTH) {
            tempClause = (int*) malloc(sizeof(int) * STOREBLOCK);
            freeStore = STOREBLOCK;
        }
        clause[i] = tempClause;
        clauseSize = 0;
        do {
            r = fscanf(fp, "%i", &lit);
            if (lit != 0) {
                clauseSize++;
                *tempClause++ = lit;
                numOccurrenceT[numVars + lit]++;
            } else {
                *tempClause++ = 0; //0 sentinel as literal!
            }
            freeStore--;
        } while (lit != 0);
        if (clauseSize > maxClauseSize)
            maxClauseSize = clauseSize;
        if (clauseSize < minClauseSize)
            minClauseSize = clauseSize;
    }

    for (i = 0; i < numLiterals + 1; i++) {
        occurrence[i] = (int*) malloc(sizeof(int) * (numOccurrenceT[i] + 1));
        if (numOccurrenceT[i] > maxNumOccurences)
            maxNumOccurences = numOccurrenceT[i];
    }

    for (i = 1; i <= numClauses; i++) {
        j = 0;
        while ((lit = clause[i][j])) {
            occurrence[lit + numVars][numOccurrence[lit + numVars]++] = i;
            j++;
        }
        occurrence[lit + numVars][numOccurrence[lit + numVars]] = 0; //sentinel at the end!
    }
    probs = (double*) malloc(sizeof(double) * (numVars + 1));
    breaks = (int*) malloc(sizeof(int) * (numVars + 1));
    free(numOccurrenceT);
    fclose(fp);
}

static inline void init() {
    int i, j;
    int critLit = 0, lit;
    numFalse = 0;
    for (i = 1; i <= numClauses; i++) {
        numTrueLit[i] = 0;
        whereFalse[i] = -1;
    }

    for (i = 1; i <= numVars; i++) {
        breaks[i] = 0;
    }
    //pass trough all clauses and apply the assignment previously generated
    for (i = 1; i <= numClauses; i++) {
        j = 0;
        while ((lit = clause[i][j])) {
            if (atom[abs(lit)] == (lit > 0)) {
                numTrueLit[i]++;
                critLit = lit;
            }
            j++;
        }
        if (numTrueLit[i] == 1) {
            //if the clause has only one literal that causes it to be sat,
            //then this var. will break the sat of the clause if flipped.
            critVar[i] = abs(critLit);
            breaks[abs(critLit)]++;
        } else if (numTrueLit[i] == 0) {
            //add this clause to the list of unsat caluses.
            falseClause[numFalse] = i;
            whereFalse[i] = numFalse;
            numFalse++;
        }
    }
}

/** Checks whether the assignment from atom is a satisfying assignment.*/
static inline int checkAssignment(int expectedFailed = 0) {
    int i, j;
    int sat, lit;
    int failed = 0;
    for (i = 1; i <= numClauses; i++) {
        sat = 0;
        j = 0;
        while ((lit = clause[i][j])) {
            if (atom[abs(lit)] == (lit > 0))
                sat = 1;
            j++;
        }
        if (sat == 0) {
            ++failed;
        }
    }

    if (failed != expectedFailed) {
        throw std::runtime_error("FIASKO");
    }

    return failed;
}

//go trough the unsat clauses with the flip counter and DO NOT pick RANDOM unsat clause!!
// do not cache the break values but compute them on the fly (this is also the default implementation of WalkSAT in UBCSAT)
static inline void pickAndFlipNC() {
    int i, j;
    int bestVar;
    int rClause, tClause;
    rClause = falseClause[flip % numFalse]; //random unsat clause
    bestVar = abs(clause[rClause][0]);
    double randPosition;
    int lit;
    double sumProb = 0;
    int xMakesSat = 0;
    i = 0;
    while ((lit = clause[rClause][i])) {
        breaks[i] = 0;
        j=0;
        while ((tClause = occurrence[numVars - lit][j])){
            if (numTrueLit[tClause] == 1)
                breaks[i]++;
            j++;
        }
        probs[i] = probsBreak[breaks[i]];
        sumProb += probs[i];
        i++;
    }
    randPosition = (double) (rand()) / RAND_MAX * sumProb;
    for (i = i - 1; i != 0; i--) {
        sumProb -= probs[i];
        if (sumProb <= randPosition)
            break;
    }
    bestVar = abs(clause[rClause][i]);

    //flip bestvar
    if (atom[bestVar])
        xMakesSat = -bestVar; //if x=1 then all clauses containing -x will be made sat after fliping x
    else
        xMakesSat = bestVar; //if x=0 then all clauses containing x will be made sat after fliping x
    atom[bestVar] = 1 - atom[bestVar];
    //1. Clauses that contain xMakeSAT will get SAT if not already SAT
    //numOccurenceX = numOccurrence[numVars + xMakesSat];
    i = 0;
    while ((tClause = occurrence[xMakesSat + numVars][i])) {
        //if the clause is unsat it will become SAT so it has to be removed from the list of unsat-clauses.
        if (numTrueLit[tClause] == 0) {
            //remove from unsat-list
            falseClause[whereFalse[tClause]] = falseClause[--numFalse]; //overwrite this clause with the last clause in the list.
            whereFalse[falseClause[numFalse]] = whereFalse[tClause];
            whereFalse[tClause] = -1;
        }
        numTrueLit[tClause]++; //the number of true Lit is increased.
        i++;
    }
    //2. all clauses that contain the literal -xMakesSat=0 will not be longer satisfied by variable x.
    //all this clauses contained x as a satisfying literal
    //numOccurenceX = numOccurrence[numVars - xMakesSat];
    i = 0;
    while ((tClause = occurrence[numVars - xMakesSat][i])) {
        if (numTrueLit[tClause] == 1) { //then xMakesSat=1 was the satisfying literal.
            falseClause[numFalse] = tClause;
            whereFalse[tClause] = numFalse;
            numFalse++;
        }
        numTrueLit[tClause]--;
        i++;
    }
    //fliping done!
}
static inline void pickAndFlip() {
    int var;
    int rClause = falseClause[flip % numFalse];
    double sumProb = 0.0;
    double randPosition;
    int i, j;
    int tClause; //temporary clause variable
    int xMakesSat; //tells which literal of x will make the clauses where it appears sat.
    i = 0;
    while ((var = abs(clause[rClause][i]))) {
        probs[i] = probsBreak[breaks[var]];
        sumProb += probs[i];
        i++;
    }
    randPosition = (double) (rand()) / RAND_MAX * sumProb;
    for (i = i - 1; i != 0; i--) {
        sumProb -= probs[i];
        if (sumProb <= randPosition)
            break;
    }
    bestVar = abs(clause[rClause][i]);

    if (atom[bestVar] == 1)
        xMakesSat = -bestVar; //if x=1 then all clauses containing -x will be made sat after fliping x
    else
        xMakesSat = bestVar; //if x=0 then all clauses containing x will be made sat after fliping x

    atom[bestVar] = 1 - atom[bestVar];

    //1. all clauses that contain the literal xMakesSat will become SAT, if they where not already sat.
    i = 0;
    while ((tClause = occurrence[xMakesSat + numVars][i])) {
        //if the clause is unsat it will become SAT so it has to be removed from the list of unsat-clauses.
        if (numTrueLit[tClause] == 0) {
            //remove from unsat-list
            falseClause[whereFalse[tClause]] = falseClause[--numFalse]; //overwrite this clause with the last clause in the list.
            whereFalse[falseClause[numFalse]] = whereFalse[tClause];
            whereFalse[tClause] = -1;
            critVar[tClause] = abs(xMakesSat); //this variable is now critically responsible for satisfying tClause
            //adapt the scores of the variables
            //the score of x has to be decreased by one because x is critical and will break this clause if fliped.
            breaks[bestVar]++;
        } else {
            //if the clause is satisfied by only one literal then the score has to be increased by one for this var.
            //because fliping this variable will no longer break the clause
            if (numTrueLit[tClause] == 1) {
                breaks[critVar[tClause]]--;
            }
        }
        //if the number of numTrueLit[tClause]>=2 then nothing will change in the scores
        numTrueLit[tClause]++; //the number of true Lit is increased.
        i++;
    }
    //2. all clauses that contain the literal -xMakesSat=0 will not be longer satisfied by variable x.
    //all this clauses contained x as a satisfying literal
    i = 0;
    while ((tClause = occurrence[numVars - xMakesSat][i])) {
        if (numTrueLit[tClause] == 1) { //then xMakesSat=1 was the satisfying literal.
            //this clause gets unsat.
            falseClause[numFalse] = tClause;
            whereFalse[tClause] = numFalse;
            numFalse++;
            //the score of x has to be increased by one because it is not breaking any more for this clause.
            breaks[bestVar]--;
            //the scores of all variables have to be increased by one ; inclusive x because flipping them will make the clause again sat
        } else if (numTrueLit[tClause] == 2) { //find which literal is true and make it critical and decrease its score
            j = 0;
            while ((var = abs(clause[tClause][j]))) {
                if (((clause[tClause][j] > 0) == atom[abs(var)])) { //x can not be the var anymore because it was flipped //&&(xMakesSat!=var)
                    critVar[tClause] = var;
                    breaks[var]++;
                    break;
                }
                j++;
            }
        }
        numTrueLit[tClause]--;
        i++;
    }

}


static inline void printEndStatistics() {
    printf("\nc EndStatistics:\n");
    printf("c %-30s: %-9lli\n", "numFlips", flip);
    printf("c %-30s: %-8.2f\n", "avg. flips/variable", (double) flip / (double) numVars);
    printf("c %-30s: %-8.2f\n", "avg. flips/clause", (double) flip / (double) numClauses);
}

void initPoly() {
    int i;
    probsBreak = (double*) malloc(sizeof(double) * (maxNumOccurences + 1));
    for (i = 0; i <= maxNumOccurences; i++) {
        probsBreak[i] = pow((eps + i), -cb);
    }
}

void initExp() {
    int i;
    probsBreak = (double*) malloc(sizeof(double) * (maxNumOccurences + 1));
    for (i = 0; i <= maxNumOccurences; i++) {
        probsBreak[i] = pow(cb, -i);
    }
}

void parseParameters(int argc, char *argv[]) {
    //define the argument parser
    static struct option long_options[] =
            { { "fct", required_argument, 0, 'f' }, { "caching", required_argument, 0, 'c' }, { "eps", required_argument, 0, 'e' }, { "cb", required_argument, 0, 'b' }, { "runs", required_argument, 0, 't' }, { "maxflips", required_argument, 0, 'm' }, { "help", no_argument, 0, 'h' }, { 0, 0, 0, 0 } };

    while (optind < argc) {
        int index = -1;
        struct option * opt = 0;
        int result = getopt_long(argc, argv, "f:e:c:b:t:m:h", long_options, &index); //
        if (result == -1)
            break; /* end of list */
        switch (result) {
            case 'h':
                exit(0);
                break;
            case 'c':
                caching = atoi(optarg);
                caching_spec = 1;
                break;
            case 'f':
                fct = atoi(optarg);
                fct_spec = 1;
                break;
            case 'e':
                eps = atof(optarg);
                if (eps <= 0) {
                    printf("\nERROR: eps should >0!!!\n");
                    exit(0);
                }
                break;
            case 'b':
                cb = atof(optarg);
                cb_spec = 1;
                break;
            case 't': //maximum number of tries to solve the problems within the maxFlips
                maxTries = atoi(optarg);
                break;
            case 'm': //maximum number of flips to solve the problem
                maxFlips = atoi(optarg);
                break;
            case 0: /* all parameter that do not */
                /* appear in the optstring */
                opt = (struct option *) &(long_options[index]);
                printf("'%s' was specified.", opt->name);
                if (opt->has_arg == required_argument)
                    printf("Arg: <%s>", optarg);
                printf("\n");
                break;
            default:
                printf("parameter not known!\n");
                exit(0);
                break;
        }
    }
    if (optind == argc) {
        printf("ERROR: Parameter String not correct!\n");
        exit(0);
    }
    fileName = *(argv + optind);

    if (argc > optind + 1) {
        seed = atoi(*(argv + optind + 1));
        if (seed == 0)
            printf("c there might be an error in the command line or is your seed 0?");
    } else
        seed = time(0);
}

void setupParameters() {
    if (!caching_spec) {
        if (maxClauseSize <= 3){
            pickAndFlipVar = pickAndFlipNC; //no caching of the break values in case of 3SAT
            caching =0;
        }
        else{
            pickAndFlipVar = pickAndFlip; //cache the break values for other k-SAT
            caching = 1;
        }
    }
    else{
        if (caching)
            pickAndFlipVar = pickAndFlip; //cache the break values for other k-SAT
        else
            pickAndFlipVar = pickAndFlipNC; //no caching of the break values in case of 3SAT
    }
    if (!cb_spec) {
        if (maxClauseSize <= 3) {
            cb = 2.06;
            eps = 0.9;

        } else if (maxClauseSize <= 4)
            cb = 2.85;
        else if (maxClauseSize <= 5)
            cb = 3.7;
        else if (maxClauseSize <= 6)
            cb = 5.1;
        else
            cb = 5.4;
    }
    if (!fct_spec) {
        if (maxClauseSize < 4)
            fct = 0;
        else
            fct = 1;
    }
    if (fct == 0)
        initLookUpTable = initPoly;
    else
        initLookUpTable = initExp;
}

double totalTime = 0;
std::vector<size_t> vars_permutation;

bool MakeIteration(uint64_t iteration_idx) {
    static const size_t merging_block_size = 4;
    static std::vector<char> dummyCopyLitValue;
    static std::vector<char> bestKnownLitValue;
    static std::random_device rd;
    static std::mt19937 eng(seed);

    dummyCopyLitValue = atom;
    bestKnownLitValue = atom;

    std::shuffle(vars_permutation.begin() + 1, vars_permutation.end(), eng); // 0 is reserved
    bestNumFalse = numClauses;

    for (size_t merge_var_idx = 0; merge_var_idx <= (numVars + merging_block_size - 1) / merging_block_size; ++merge_var_idx) {
        uint64_t init_merge_var_mask = 0;
        for (size_t var_sub_idx = 0; var_sub_idx < merging_block_size; ++var_sub_idx) {
            size_t atomIdx = merge_var_idx * merging_block_size + var_sub_idx;
            size_t varIdx = vars_permutation[atomIdx + 1];
            init_merge_var_mask = (init_merge_var_mask << 1u) | atom[varIdx];
        }

        for (uint64_t merge_var_mask = init_merge_var_mask; merge_var_mask < (1u << merging_block_size); ++merge_var_mask) {
            uint64_t tmp_merge_var_mask = merge_var_mask;
            for (size_t var_sub_idx = merging_block_size; var_sub_idx >= 1; --var_sub_idx) {
                size_t atomIdx = merge_var_idx * merging_block_size + var_sub_idx - 1;
                size_t varIdx = vars_permutation[atomIdx + 1];
                atom[varIdx] = tmp_merge_var_mask % 2u;
                tmp_merge_var_mask >>= 1u;
            }

            for (flip = 0; flip < maxFlips; ++flip) {
                init();
                pickAndFlip();

                if (numFalse < bestNumFalse) {
                    printf("numFalse %d\n", numFalse);
                    checkAssignment(numFalse);
                    bestNumFalse = numFalse;
                    bestKnownLitValue = atom;

                    if (numFalse < 1100) {
                        atom = bestKnownLitValue;
                        return true;
                    }
                }
            }

            atom = dummyCopyLitValue;
        }
    }

    atom = bestKnownLitValue;
    return false;
}

int main(int argc, char *argv[]) {
    parseParameters(argc, argv);
    parseFile();
    printFormulaProperties();
    setupParameters(); //call only after parsing file!!!
    initLookUpTable(); //Initialize the look up table
    printSolverParameters();
    srand(seed);

    vars_permutation.resize(numVars + 1);
    for (size_t i = 0; i <= numVars; ++i) {
        vars_permutation[i] = i;
    }

    for (int tryy = 0; tryy < maxTries; tryy++) {
        if (MakeIteration(tryy)) {
            printSolution();
            printf("finished\n");
            break;
        }
    }

    printEndStatistics();
    return 0;
}