#ifndef __SOLVER_H
#define __SOLVER_H

#include "parser.h"
#include "clause.h"
#include "opstack.h"
#include "heap.h"
#include <cmath>
#include <cstdlib>
#include <vector>
#include <algorithm>
#include <unordered_set>
#include <iostream>
#include <ctime>
#include <chrono>
using namespace std;


extern int solveDone;

struct Temptable {

public:

    vector<int> table;

    inline void init(int sz) {
        table = vector<int>(sz+4);
        timestamp = vector<int>(sz+4, -1);
        nowT = 0;
    }

    inline void clear() {
        ++nowT;
    }

    inline int get(int id) {
        // Return -1 if unset yet
        int is_val = (timestamp[id] == nowT);
        return table[id] * is_val - !is_val;
    }

    inline void set(int id, unsigned int val) {
        table[id] = val;
        timestamp[id] = nowT;
    }


protected:

    vector<int> timestamp;
    int nowT = 0;

};

class solver {

public:
    struct WatcherInfo {
        int clsid, wid;
        int prev=-1, next=-1;
        WatcherInfo() {};
        WatcherInfo(int clsidt, int widt)
        {
            clsid = clsidt;
            wid = widt;
        }
    };

    typedef pair<int,int> pii;
    enum {
        INFINITE = 1023456789,
        LEARN_UNSAT = 1,
        LEARN_ASSIGNMENT = 2,
        LEARN_CLAUSE = 3,
        MOM = 4,                // 100
        VSIDS = 8,              // 1000
        JW = 16,                // 10000
        DFS = 32
    };
    static const int clauseSzThreshold = 10;

    // Init via CNF file
    void init(const char *filename, int mode);
    bool solve();
    inline vector<int> result();
    inline void printCNF();
    inline int size();
    int runMode;

    int timeout;

    time_t startTime;
    int runTime;

protected:
    int unsatAfterInit = 0;
    int sat = 1;



    int maxVarIndex;
    int oriClsNum;
    vector<Clause> clauses;
    vector<int> unit;
    opStack var;
    int nowLevel = 0;

    bool dfs(int var, bool sign);

    // Helper function for DPLL
    bool set(int var, bool val, int src=-1);
    void backtrack(int lv);
    int learnFromConflict(int &vid, int &sign, int &src);
    //bool restart();
    void initAllWatcherList();
    void initWatcherList(int cid);

    bool _solve();
    int conflictingClsID = -1;
    Temptable litMarker;
    Temptable delMarker;
    inline int _resolve(int clsid, int x);


    // Preprocess
    bool preprocess();
    bool preNessasaryAssignment();
    bool simplifyClause();
    void simplifyResolve(vector< unordered_set<int> > &dict);
    void preInferCls(vector< unordered_set<int> > &dict);


    // Clause helper function
    inline bool evalClauesLit(int clsid, int id) const;
    inline bool evalClauesLit(const Clause &cls, int id) const;
    inline bool evalClauesWatchedLit(const WatcherInfo &info) const;
    inline bool evalClauesWatchedLit(int clsid, int wid) const;
    inline bool evalClauesWatchedLit(const Clause &cls, int wid) const;
    inline int updateClauseWatcher(const WatcherInfo &info);
    inline int updateClauseWatcher(int clsid, int wid);
    inline int updateClauseWatcher(Clause &cls, int wid);


    // 2 Literal Watching
    vector<WatcherInfo> watchers;
    vector<int> pos;
    vector<int> neg;

    // 2 Literal Watching helper function
    inline int getLit(const WatcherInfo &info) const;
    inline int getVar(const WatcherInfo &info) const;
    inline int getSign(const WatcherInfo &info) const;
    inline int getVal(const WatcherInfo &info) const;
    inline bool eval(const WatcherInfo &info) const;

    // Conflict Clause Learning Heuristic
    vector<int> nowLearnt;
    vector<int> firstUIP();
    void minimizeLearntCls();
    bool isFromUIP(int vid, int sign);

    // Branching Heuristic
    VarHeap varPriQueue;
    vector<int> phaseRecord;

    void initHeuristic();
    pii pickUnassignedVar();
    int pickBalancedPhase(int vid);


};


// Return result
inline vector<int> solver::result() {
    if (!sat) {
        if(runTime>timeout)
            return vector<int>(1, -1);
        else
            return vector<int>(1, 0);
    }

    vector<int> ret(maxVarIndex+1, 1);
    for(int i=1; i<=maxVarIndex; ++i)
        ret[i] = var.getVal(i) ? i : -i;
    return ret;
}

inline void solver::printCNF() {
    for(auto &cls : clauses) {
        for(int i=0; i<cls.size(); ++i)
            printf("%d ", cls.getLit(i));
        printf("0\n");
    }
}

inline int solver::size() {
    return maxVarIndex;
}


// Resolve helper
inline int solver::_resolve(int clsid, int x) {

    int ret = 0;
    for(int i=0; i<clauses[clsid].size(); ++i) {
        int lit = clauses[clsid].getLit(i);
        int vid = clauses[clsid].getVar(i);
        int sign = clauses[clsid].getSign(i);
        if( vid == x || litMarker.get(vid) == sign ) continue;
        if( litMarker.get(vid) != -1 ) return -1;
        litMarker.set(vid, sign);
        varPriQueue.increasePri(vid, 1.0-VarHeap::decayFactor, sign);
        if( var.getLv(vid) == nowLevel )
            ++ret;
        else
            nowLearnt.push_back(lit);
    }

    return ret;

}


// Clause helper function
inline bool solver::evalClauesLit(int clsid, int id) const {
    return evalClauesLit(clauses[clsid], id);
}
inline bool solver::evalClauesLit(const Clause &cls, int id) const {
    return var.getVal(cls.getVar(id)) == cls.getSign(id);
}

inline bool solver::evalClauesWatchedLit(const WatcherInfo &info) const {
    return evalClauesWatchedLit(info.clsid, info.wid);
}
inline bool solver::evalClauesWatchedLit(int clsid, int wid) const {
    return evalClauesWatchedLit(clauses[clsid], wid);
}
inline bool solver::evalClauesWatchedLit(const Clause &cls, int wid) const {
    return evalClauesLit(cls, cls.watcher[wid]);
}

inline int solver::updateClauseWatcher(const WatcherInfo &info) {
    return updateClauseWatcher(info.clsid, info.wid);
}
inline int solver::updateClauseWatcher(int clsid, int wid) {
    return updateClauseWatcher(clauses[clsid], wid);
}
inline int solver::updateClauseWatcher(Clause &cls, int wid) {

    for(int counter=cls.size(); counter; --counter) {

        cls.watchNext(wid);
        if( !cls.watchSame() &&
                (var.getVal(cls.getWatchVar(wid)) == 2 || evalClauesWatchedLit(cls, wid)) )
            return cls.getWatchLit(wid);

    }
    return cls.getWatchLit(wid);

}


// 2 Literal Watching helper function
inline int solver::getLit(const WatcherInfo &info) const {
    return clauses[info.clsid].getWatchLit(info.wid);
}
inline int solver::getVar(const WatcherInfo &info) const {
    return clauses[info.clsid].getWatchVar(info.wid);
}
inline int solver::getSign(const WatcherInfo &info) const {
    return clauses[info.clsid].getWatchSign(info.wid);
}
inline int solver::getVal(const WatcherInfo &info) const {
    return var.getVal(getVar(info));
}
inline bool solver::eval(const WatcherInfo &info) const {
    return evalClauesWatchedLit(clauses[info.clsid], info.wid);
}


#endif
