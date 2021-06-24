#include "solver.h"

bool solver::dfs(int vid, bool sign)
{
    time_t now;
    time(&now);
    runTime = difftime(now, startTime);
    if (runTime > timeout) return false;
    //cout<<nowLevel<<endl;
    if (vid <= maxVarIndex) {
        if (vid != 0)
            var.set(vid, sign, vid, -1);
        bool ret = dfs(vid+1, 0);
        var.backToLevel(vid);
        ret |= dfs(vid+1, 1);
        var.backToLevel(vid);
        return ret;
    }
    else if (vid != 0) {
        bool sat = true;
        //check valid
        for (auto &cls : clauses){
            bool allZero = true;
            for (int i=0;i<cls.size();i++){
                if (evalClauesLit(cls, i)){
                    allZero = false;
                }
            }
            if(allZero){
                sat = false;
                break;
            }
        }
        return sat;
    }
    return false;
}


// Solver helper function
static bool satisfyAlready(const vector<int> &cls) {
    unordered_set<int> checker;
    for(auto &v : cls) {
        if( checker.find(-v) != checker.end() )
            return true;
        checker.insert(v);
    }
    return false;
}

static void appendListWatcher(vector<solver::WatcherInfo> &pool, int &head, int eleid) {
    // Empty case
    if( head == -1 ) {
        head = eleid;
        pool[eleid].prev = pool[eleid].next = eleid;
        return;
    }
    int prev = pool[head].prev;
    pool[eleid].next = head;
    pool[eleid].prev = prev;
    pool[prev].next = eleid;
    pool[head].prev = eleid;
}

static void swapListWatcher(vector<solver::WatcherInfo> &pool, int &from, int &to, int eleid) {
    // Check list head
    if( eleid == from ) {
        if( pool[from].next == from )
            from = -1;
        else
            from = pool[eleid].next;
    }
    // Remove from current list
    pool[pool[eleid].prev].next = pool[eleid].next;
    pool[pool[eleid].next].prev = pool[eleid].prev;
    // Add to target list
    appendListWatcher(pool, to, eleid);
}

// static inline int __idx(int lit) {
//     return (abs(lit)<<1) + (lit>0);
// }

// Init solver with cnf file
void solver::init(const char *filename, int mode) {

    // Init with empty solver
    *this = solver();
    runMode = mode;
    // Get raw clause from cnf file
    vector< vector<int> > raw;
    parse_DIMACS_CNF(raw, maxVarIndex, filename);

    //cout<<"run mode after init "<<runMode<<endl;

    if((runMode & DFS)){
        var = opStack(maxVarIndex+4);
        for(auto &cls : raw) {
            if( cls.empty() ) unsatAfterInit = 1;
            else if( !satisfyAlready(cls) ) {
                clauses.push_back(Clause());
                clauses.back().watcher[0] = 0;
                clauses.back().watcher[1] = (cls.size() >> 1);
                clauses.back().simpleCnt[0] = 0;
                clauses.back().simpleCnt[1] = 0;
                clauses.back().lit = move(cls);
            }
        }
        nowLevel = 0;
    }
    else{
        // Init assignment stack
        var = opStack(maxVarIndex+4);

        // Init container for learnt clause
        nowLearnt.resize(maxVarIndex<<1+4);

        // Init temp table
        litMarker.init(maxVarIndex+4);
        delMarker.init(maxVarIndex+4);

        // Init heuristic
        varPriQueue.init(maxVarIndex);

        for(auto &cls : raw) {
            if( cls.empty() ) unsatAfterInit = 1;
            else if( cls.size() == 1 ) unit.emplace_back(cls[0]);
            else if( !satisfyAlready(cls) ) {
                clauses.push_back(Clause());
                clauses.back().watcher[0] = 0;
                clauses.back().watcher[1] = (cls.size() >> 1);
                clauses.back().simpleCnt[0] = 0;
                clauses.back().simpleCnt[1] = 0;
                clauses.back().lit = move(cls);
            }
        }


        // Init two watching check list
        initAllWatcherList();


        // Assign and run BCP for all unit clause
        nowLevel = 0;
        if( unit.size() ) {
            for(auto lit : unit)
                unsatAfterInit |= !set(abs(lit), lit>0);
            if(!unsatAfterInit)
                simplifyClause();
        }
    }


}

// Assign id=val@nowLevel and run BCP recursively
bool solver::set(int id, bool val, int src) {

    if( solveDone ) return false;

    // If id is already set, check consistency
    if( var.getVal(id) != 2 ) {
        conflictingClsID = -1;
        return var.getVal(id) == val;
    }
    //cout<<"SC "<<id<<" "<<val<<" from "<<src<<endl;
    if( nowLevel == 0 ) src = -1;

    // Set id=val@nowLevel
    var.set(id, val, nowLevel, src);
    // Update 2 literal watching
    bool ret = true;

    int &head = (val ? neg[id] : pos[id]);
    //cout<<head<<endl;
    int idx = head;
    while( idx != -1 ) {

        WatcherInfo &now = watchers[idx];
        int next = (now.next == head ? -1 : now.next);
        //cout<<idx<<endl;
        // Update watcher
        updateClauseWatcher(now);
        //cout<<"updated"<<getVal(now)<<" "<<eval(now)<<endl;
        if( getVal(now) == 2 || eval(now) ) {
            //Case1
            //cout<<"c1"<<endl;
            // Watcher reaches an pending/satisfied variable

            // Push this watcher to corresponding check list
            if( getSign(now) )
                swapListWatcher(watchers, head, pos[getVar(now)], idx);
            else
                swapListWatcher(watchers, head, neg[getVar(now)], idx);

        }
        else {
            // Watcher run through all clause back to original one
            // Can't find next literal to watch

            // b = alternative watcher in this clause
            WatcherInfo b(now.clsid, now.wid^1);
            //cout<<"b"<<getVal(b)<<" "<<eval(b)<<endl;
            //Case2
            if( getVal(b) == 2 ) {
                //cout<<"c2"<<endl;
                if( !set(getVar(b), getSign(b), now.clsid) ) {

                    ret = false;
                    break;
                }
            }
            //Case4
            else if( !eval(b) ) {
                //cout<<"c4"<<endl;
                //cout<<"unitfailed!"<<endl;
                conflictingClsID = now.clsid;
                ret = false;
                break;
            }
            //else Case3
        }

        idx = next;

    }
    //cout<<"done!"<<id<<" "<<ret<<" at "<<nowLevel<<" "<<src<<endl;
    // BCP done successfully without conflict
    return ret;

}


void solver::backtrack(int lv) {
    for(int i=var._top; i>=0 && var.stk[i].lv>lv; --i)
        varPriQueue.restore(var.stk[i].var);
    var.backToLevel(lv);
}


// Conflicting.
// It will backtrack to the decision level
// where causing conflict clause become unit
// and set vid, sign, src indicating unit variable information.
int solver::learnFromConflict(int &vid, int &sign, int &src) {

    vector<int> learnt = firstUIP();
    if( learnt.empty() )
        return LEARN_UNSAT;

    // Determined non-chronological backtracking
    int backlv = 0;
    int towatch = -1;
    for(int i=learnt.size()-2; i>=0; --i)
        if( var.getLv(abs(learnt[i])) > backlv ) {
            backlv = var.getLv(abs(learnt[i]));
            towatch = i;
        }

    // Learn one assignment
    if( learnt.size() == 1 || backlv == 0 ) {
        backtrack(0);
        nowLevel = 0;
        int uip = learnt.back();
        if( !set(abs(uip), uip>0) )
            return LEARN_UNSAT;
        unit.emplace_back(uip);
        return LEARN_ASSIGNMENT;
    }

    // Add conflict clause
    clauses.push_back(Clause());
    clauses.back().watcher[0] = towatch;           // Latest
    clauses.back().watcher[1] = learnt.size() - 1; // Learnt
    clauses.back().lit = move(learnt);
    watchers.resize(watchers.size()+2);
    initWatcherList(clauses.size()-1);

    backtrack(backlv);
    nowLevel = backlv;
    vid = clauses.back().getWatchVar(1);
    sign = clauses.back().getWatchSign(1);
    src = clauses.size()-1;

    return LEARN_CLAUSE;

}

void solver::initAllWatcherList() {
    watchers = vector<WatcherInfo>(clauses.size()<<1);
    pos = vector<int>(maxVarIndex+4, -1);
    neg = vector<int>(maxVarIndex+4, -1);

    for(int cid=0; cid<clauses.size(); ++cid) {
        clauses[cid].watcher[0] = 0;
        clauses[cid].watcher[1] = (clauses[cid].size() >> 1);
        initWatcherList(cid);
    }

}

void solver::initWatcherList(int cid) {

    Clause &cls = clauses[cid];
    int id = cls.getWatchVar(0);
    int wid1 = (cid<<1);
    int wid2 = (cid<<1) + 1;
    //cout<<"init"<< cid<<endl;
    watchers[wid1] = WatcherInfo(cid, 0);
    if( cls.getWatchSign(0) )
        appendListWatcher(watchers, pos[id], wid1);
    else
        appendListWatcher(watchers, neg[id], wid1);

    id = cls.getWatchVar(1);
    watchers[wid2] = WatcherInfo(cid, 1);
    //cout<<id<<endl;
    if( cls.getWatchSign(1) )
        appendListWatcher(watchers, pos[id], wid2);
    else
        appendListWatcher(watchers, neg[id], wid2);
    //cout<<"init"<< cid<<endl;
}


bool solver::solve() {
    time(&startTime);
    if((runMode & DFS)){
        sat = dfs(0, 0);
    }
    else{
        if( unsatAfterInit ) return sat = false;
        // Preprocessing for given problem
        // Init database with all clause which has 2 or more literal in raw database
        // Eliminate all unit clause and check whether there is empty clause
        if(!preprocess())
            return sat = false;
        // Init heuristic
        initHeuristic();
        sat = _solve();
    }

    return sat;
}

bool solver::_solve() {

    // Main loop for DPLL
    while( true ) {

        ++nowLevel;
        pii decision = pickUnassignedVar();
        if( decision.first == -1 )
            return true;
        time_t now;
        time(&now);
        runTime = difftime(now, startTime);
        if(runTime>timeout) return false;
        int vid = decision.first;
        int sign = decision.second;
        int src = -1;
        //cout<<vid<<endl;
        while( !set(vid, sign, src) ) {
            //if( solveDone ) return false;
            //cout<<conflictingClsID<<endl;
            if( conflictingClsID == -1 )
                return false;

            int learnResult = learnFromConflict(vid, sign, src);
            //cout<<learnResult<<endl;
            if((learnResult == LEARN_UNSAT))
                return false;
            else if( learnResult == LEARN_ASSIGNMENT )
                break;
        }

    }

    return false;
}


/******************************************************
    Preprocessing
******************************************************/
bool solver::preprocess() 
{
    if( !simplifyClause() )
        return false;
    return true;
}


bool solver::simplifyClause() {
    int cid=0;
    while( cid < clauses.size() ) {
        bool satisfied = false;
        int lid = 0;
        while( lid < clauses[cid].size() ) {
            int vid = clauses[cid].getVar(lid);
            int sign = clauses[cid].getSign(lid);
            int now = var.getVal(vid);
            if( now==2 ) ++lid;
            else if( now==sign ) {
                satisfied = true;
                break;
            }
            else {
                swap(clauses[cid].lit[lid], clauses[cid].lit.back());
                clauses[cid].lit.pop_back();
            }
        }

        if( clauses.empty() ) return false;
        if( satisfied ) {
            clauses[cid] = clauses.back();
            clauses.pop_back();
        }
        else {
            clauses[cid].watcher[0] = 0;
            clauses[cid].watcher[1] = (clauses[cid].size() >> 1);
            ++cid;
        }
    }
    oriClsNum = clauses.size();
    initAllWatcherList();

    return true;
}


/******************************************************
    Implementing Conflict Analysis and Learning Heuristic
******************************************************/
vector<int> solver::firstUIP() 
{
    // VSIDS
    if((runMode & VSIDS))
        varPriQueue.decayAll();

    // Init
    litMarker.clear();
    nowLearnt.clear();
    int todoNum = _resolve(conflictingClsID, -1);
    if (todoNum == -1)
        return vector<int>();

    // Resolve and find 1UIP
    int top = var._top;
    while( todoNum > 1 ) {
        while( litMarker.get(var.stk[top].var) == -1 )
            --top;
        int nowNum = _resolve(var.stk[top].src, var.stk[top].var);
        if( nowNum == -1 )
            return vector<int>();
        todoNum += nowNum - 1;
        --top;
    }

    // Put 1UIP at back of the vector
    while( litMarker.get(var.stk[top].var) == -1 )
        --top;
    int uip = (var.stk[top].val > 0 ? -var.stk[top].var : var.stk[top].var);
    nowLearnt.push_back(uip);

    // Minimization
    minimizeLearntCls();

    return nowLearnt;

}


void solver::minimizeLearntCls() {

    // Minimize clause
    litMarker.clear();
    delMarker.clear();
    for(unsigned int i=0; i<nowLearnt.size(); ++i)
        litMarker.set(abs(nowLearnt[i]), nowLearnt[i]>0);
    int eliminateNum = 0;

    // Check all literals in learnt clause except 1UIP
    for(int i=nowLearnt.size()-2; i>=0; --i) {
        int src = var.getSrc(abs(nowLearnt[i]));
        if( src == -1 )
            continue;

        bool selfSubsumed = true;
        for(int j=0; j<clauses[src].size(); ++j) {
            int vid = clauses[src].getVar(j);
            int sign = clauses[src].getSign(j)>0;
            if( abs(nowLearnt[i])!=vid && !isFromUIP(vid, sign) ) {
                selfSubsumed = false;
                break;
            }
        }
        if( selfSubsumed ) {
            ++eliminateNum;
            delMarker.set(i, 1);
        }
    }
    if( eliminateNum ) {
        int j = -1;
        for(unsigned int i=0; i<nowLearnt.size(); ++i)
            if( delMarker.get(i) == -1 )
                nowLearnt[++j] = nowLearnt[i];
        nowLearnt.resize(j+1);
    }

}


bool solver::isFromUIP(int vid, int sign) {

    if( litMarker.get(vid) != -1 )
        return litMarker.get(vid) == sign;

    int src = var.getSrc(vid);
    if( src == -1 ) {
        litMarker.set(vid, 2);
        return false;
    }

    for(int i=0; i<clauses[src].size(); ++i) {
        int nv = clauses[src].getVar(i);
        int ns = clauses[src].getSign(i);
        if( nv!=vid && isFromUIP(nv, ns) == false ) {
            litMarker.set(vid, 2);
            return false;
        }
    }
    litMarker.set(vid, sign);
    return true;

}


/******************************************************
    Implementing Branching Heuristic
******************************************************/
void solver::initHeuristic() {
    //MOM
    if((runMode & MOM)){
        for(auto &cls : clauses)
            if(cls.size()<=clauseSzThreshold)
                for(int i=0; i<cls.size(); ++i)
                    varPriQueue.increaseInitPri(cls.getVar(i), 1.0, cls.getSign(i));
    }
    // JW Score
    else if((runMode & JW)){
        for(auto &cls : clauses)
            for(int i=0; i<cls.size(); ++i)
                varPriQueue.increaseInitPri(cls.getVar(i), pow(0.5, cls.size()), cls.getSign(i));
    }
    // Random Choose
    else{
        srand(time(NULL));
        double randPri = (double) rand() / (RAND_MAX + 1.0);
        for(int i=1;i<maxVarIndex+1;i++)
                varPriQueue.increaseInitPri(i, randPri, 1);
    }
    varPriQueue.heapify();
}


pair<int,int> solver::pickUnassignedVar() {
    // Find next decision
    while (true) {
        if( varPriQueue.size() == 0 )
            return {-1, 0};
        int vid = varPriQueue.top();
        varPriQueue.pop();
        if( var.getVal(vid)==2 ){
            int sign = (varPriQueue.litBalance(vid)>0);
            return {vid, sign};
        }
    }
}
