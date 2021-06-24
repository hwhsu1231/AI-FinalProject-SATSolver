#include <cstdio>
#include <ctime>
#include <cstring>
#include <cstdlib>
#include <vector>
#include <thread>
#include <iostream>
#include <chrono>
#include <mutex>
#include <filesystem>
#include "solver.h"
using namespace std;
namespace fs = std::filesystem;


int solveDone = 0;
vector<int> result;

vector<string> conditionNameList;
vector<int> conditionEnumList;     // 測試條件
vector<string> benchmarkNameList;
vector<string> classNameList;
vector<vector<float>> classCondMeanList;


int main(int argc, const char *argv[]) {
    // if( argc < 2 ) {
    //     puts("Error: not enough arguments!");
    //     exit(1);
    // }

    srand(time(NULL));


    /* 
        MOM = 4,                // 100
        VSIDS = 8,              // 1000
        JW = 16,                // 10000
        BCP = 32,               // 100000
        CONFLICT = 64           // 1000000

        BCP                      = 32         = 32
        BCP + MOM                = 32+4       = 36
        BCP + MOM + VSIDS        = 32+4+8     = 44
        BCP + MOM + VSIDS + CDCL = 32+4+8+64  = 108
        BCP + JW                 = 32+16      = 48
        BCP + JW  + VSIDS        = 32+16+8    = 56
        BCP + JW  + VSIDS + CDCL = 32+16+8+64 = 120
     */
   
    conditionNameList.push_back("DFS           ");
    conditionNameList.push_back("CDCL          ");
    conditionNameList.push_back("CDCL+MOM+VSIDS");
    conditionNameList.push_back("CDCL+JW+VSIDS ");

    conditionEnumList.push_back(32);        // DFS
    conditionEnumList.push_back(0);         // CDCL
    conditionEnumList.push_back(12);        // CDCL + MOM + VSIDS
    conditionEnumList.push_back(24);        // CDCL + JW  + VSIDS

    fs::path maindir("benchmark");

    // 遍歷 benchmark 目錄中的子測資類別
    for (auto dirit1 : fs::directory_iterator(maindir)) 
    {   
        string className = dirit1.path().filename().u8string();
        std::cout << "Class: " << className << std::endl;
        
        vector<float> condResultSum(4, 0);
        vector<int> condResultCount(4, 0);
        vector<float> condMeanList(4, 0);

        // 遍歷類別中的測資
        for (const auto &dirit2 : fs::directory_iterator(dirit1.path()))
        {   
            std::cout << "---- [" << dirit2.path().filename().u8string() << "]" << std::endl;
            // 遍歷所有情況
            for (size_t it = 0; it < conditionEnumList.size(); it++)
            {
                solver yasat;
                auto startTime = std::chrono::high_resolution_clock::now();           // mark start time
                yasat.init(dirit2.path().u8string().c_str(), conditionEnumList[it]);  // 初始化 cnf 檔
                yasat.timeout = 5;
                yasat.solve();
                result = yasat.result();
                auto endTime = std::chrono::high_resolution_clock::now();             // mark end time
                float totalTime = 
                    std::chrono::duration<float, std::milli> (endTime - startTime).count();

                std::cout << "-------- " << conditionNameList[it] << " : ";
                if (result[0] == -1) {
                    cout << "TIMEOUT" << endl;
                }
                else if (result[0]) {
                    cout << "SATISFIABLE,   Time = " << totalTime << "ms" << endl;
                    condResultSum[it] += totalTime;
                    condResultCount[it]++;
                }
                else {
                    cout << "UNSATISFIABLE, Time = " << totalTime << "ms" << endl;
                    condResultSum[it] += totalTime;
                    condResultCount[it]++;
                }
            }
        }

        classNameList.push_back(className);

        for (size_t it = 0; it < conditionEnumList.size(); it++) {
            if (condResultCount[it] == 0) {
                condMeanList[it] = -1;
            } else {
                condMeanList[it] = condResultSum[it] / (float)condResultCount[it];
            }
        }
        classCondMeanList.push_back(condMeanList);
    }



    std::cout << "\n\n\n";
    for (size_t it1 = 0; it1 < classNameList.size(); it1++) {
        std::cout << "Class: " << classNameList[it1] << std::endl;
        for (size_t it2 = 0; it2 < conditionNameList.size(); it2++) {
            std::cout << "---- " << conditionNameList[it2] << " = "; 
            if (classCondMeanList[it1][it2] == -1) {
                std::cout << "None" << std::endl;
            } else {
                std::cout << classCondMeanList[it1][it2] << "ms" << std::endl;
            }
            
        }
    }

#if 0
    std::vector<std::string> conditionList;
    conditionList.push_back("DFS           ");
    conditionList.push_back("CDCL          ");
    conditionList.push_back("CDCL+MOM+VSIDS");
    conditionList.push_back("CDCL+JW+VSIDS ");

    std::vector<int> conditionEnumList;     // 測試條件
    conditionEnumList.push_back(32);        // DFS
    conditionEnumList.push_back(0);         // CDCL
    conditionEnumList.push_back(12);        // CDCL + MOM + VSIDS
    conditionEnumList.push_back(24);        // CDCL + JW  + VSIDS


    std::vector<fs::path> benchmarkList;                    // 測資路徑
    std::vector<std::string> benchmarkNameList;             // 測資名稱
    std::vector<std::vector<float>> benchmarkresultList;    // 每個測資在不同情況下的結果

    // 收集測資 benchmark 目錄下的測資
    std::string path = ".\\benchmark";
    for (const auto &file : fs::directory_iterator(path)) {
        // std::cout << file.path() << std::endl;
        benchmarkList.push_back(file.path());
    }

    // Traverse Benchmarks
    for (auto bmlist : benchmarkList) {
        std::vector<float> tmpList;
        for (auto file : fs::directory_iterator(bmlist)){
            // std::cout << file.path() << std::endl;
            std::string benchmarkName = file.path().filename().u8string();
            benchmarkNameList.push_back(benchmarkName);                 // 儲存測資的名稱

            std::cout << "[" << benchmarkName << "]" << std::endl;

            // Traverse conditions
            for (size_t it = 0; it < conditionEnumList.size(); it++) {
                solver yasat;

                auto startTime = std::chrono::high_resolution_clock::now();         // mark start time
                yasat.init(file.path().u8string().c_str(), conditionEnumList[it]);  // 初始化 cnf 檔
                yasat.timeout = 1;
                yasat.solve();
                result = yasat.result();
                auto endTime = std::chrono::high_resolution_clock::now();           // mark end time
                float totalTime = 
                    std::chrono::duration<float, std::milli> (endTime - startTime).count();

                tmpList.push_back(totalTime);           // 將不同情況下的結果儲存起來
                std::cout << " -- " << conditionList[it]
                          << " = ";
                if( result[0] == -1) {
                    cout << "TIMEOUT" << endl;
                }
                else if( result[0] ) {
                    cout << "SATISFIABLE,   Time = " << totalTime << "ms" << endl;
                }
                else {
                    cout << "UNSATISFIABLE, Time = " << totalTime << "ms" << endl;
                }
            }

        }
        benchmarkresultList.push_back(tmpList);     // 將不同測資儲存起來
    }
#endif

#if 0
    fflush(stdout);
    char filename[100];
    strcpy(filename, argv[1]);
    int len = strlen(filename);
    if( len>=4  && filename[len-4]=='.' && filename[len-3] == 'c' &&
            filename[len-2] == 'n' && filename[len-1]=='f' ) {
        filename[len-3] = 's';
        filename[len-2] = 'a';
        filename[len-1] = 't';
    }
    else {
        filename[len] = '.';
        filename[len+1] = 's';
        filename[len+2] = 'a';
        filename[len+3] = 't';
        filename[len+4] = '\0';
    }
    freopen(filename, "w", stdout);


    if( result[0] ) {
        puts("s SATISFIABLE");
        putchar('v');
        for(int i=1; i<result.size(); ++i)
            printf(" %d", result[i]);
        puts(" 0");
    }
    else {
        puts("s UNSATISFIABLE");
    }
#endif

    return 0;
}
