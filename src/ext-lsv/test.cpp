#include <iostream>
#include <algorithm>
#include <string>
#include <vector>
#include <unordered_map>

using namespace std;

int main()
{
    const char *a = "123";
    string str = "some string";
    char* cstr = &str[0];
    cout << "=========================" << endl;
    // int hi = (a[0] == '1') ? 1 : 0;
    // cout << hi << endl;
    cout << "string to char* = " << cstr << endl;
    cout << "=========================" << endl;
    return 0;
}

