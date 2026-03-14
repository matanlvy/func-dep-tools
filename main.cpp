#include <iostream>
#include <vector>
#include <algorithm>
#include <iterator>
#include <cassert>
#include <sstream>
#include <set>

using namespace std;

/*
1. Go over all options for partition of 6 props to 2 sides:
   li: 1 to 5, ji:1 to n-li
2. For each such partition: go over options to choose li from n, and for that options go over options to choose ri from the remaining props
3. To choose K func_deps: for each func_dep, choose another one, check whether canonic, add more, until reaching k
4. Hold a list (or vector, etc) of isomorphic systems, the 1st system is the represtor.
5. Go over all the isomorphic lists and check whether our system is isomorphic to them. if it is - insert it into that vector.
*/

class Props
{    
public:
    vector<char> data;
    Props() = default;
    Props(const string& s)
    {
        for (char c : s)
        {
            insert(c);
        }
    }
    bool insert(char c)
    {
        if (!contains(c))
        {
            data.push_back(c);
            return true;
        }
        return false;
    }
    bool contains(char c) const
    {
        return std::count(data.begin(), data.end(), c) > 0;
    }
    bool insert(const Props& other)
    {
        bool added = false;
        for (char c : other)
        {
            if (this->insert(c)) added = true;
        }
        return added;
    }
    vector<char>::const_iterator begin() const { return data.begin(); }
    vector<char>::const_iterator end() const { return data.end(); }
    bool is_subset_of(const Props& other) const
    {
        for (char c : *this)
        {
            if (!other.contains(c)) return false;
        }
        return true;
    }
    bool operator==(const Props& other) const
    {
        return this->is_subset_of(other) && other.is_subset_of(*this);
    }
    bool operator<(const Props& other) const
    {
        return data < other.data;
    }
    friend ostream& operator<<(ostream& os, const Props& p)
    {
        for (char c : p) os << c;
        return os;
    }
    void insert(vector<char>::iterator it, char c)
    {
        data.insert(it, c);
    }

    auto erase(vector<char>::const_iterator it)
    {
        return data.erase(it);
    }

    void insert(vector<char>::const_iterator it, char c)
    {
        data.insert(it, c);
    }

    vector<char>& getData()
    {
        return data;
    }
    
    Props operator-(const Props& other) const
    {
        Props result;
        for (char c : *this)
        {
            if (!other.contains(c))
            {
                result.insert(c);
            }
        }
        return result;
    }

    Props project_onto(const Props& other) const
    {
        Props result;
        for (char c : *this)
        {
            if (other.contains(c))
            {
                result.insert(c);
            }
        }
        return result;
    }
};

class FuncDep
{    
public:
    Props l,r;
    FuncDep(const Props& l_, const Props& r_) : l(l_), r(r_) {}
    FuncDep(string l_,string r_) 
    {
        for (char c : l_)
        {
            l.insert(c);
        }
        for (char c : r_)
        {
            r.insert(c);
        }
    }
    friend ostream& operator<<(ostream& os, const FuncDep& fd)
    {
        for (char c : fd.l) os << c;
        os << "->";
        for (char c : fd.r) os << c;
        return os;
    }
    const Props& getL() const { return l; }
    const Props& getR() const { return r; }
    Props& getL() { return l; }
    Props& getR() { return r; }
};

class PropsSet: public set<Props>
{
public:
    using set<Props>::set;
    friend ostream& operator<<(ostream& os, const PropsSet& ps)
    {
        os << "{";
        bool first = true;
        for (const auto& p : ps)
        {
            if (!first) os << ", ";
            os << p;
            first = false;
        }
        os << "}";
        return os;
    }
 
};
    

class FuncSys
{    
public:
    vector<FuncDep> deps;
    Props set;
    FuncSys(vector<FuncDep> deps_, Props set_) : deps(deps_), set(set_) {}
    FuncSys(initializer_list<string> dep_strings, Props set_) : set(set_)
    {
        for (const string& s : dep_strings)
        {
            size_t pos = s.find("->");
            if (pos != string::npos) 
            {
                string left = s.substr(0, pos);
                string right = s.substr(pos + 2);
                deps.push_back(FuncDep(left, right));
            }
        }
    }
    friend ostream& operator<<(ostream& os, const FuncSys& fs)
    {
        os << "{";
        bool first = true;
        for (const auto& dep : fs.deps)
        {
            if (!first) os << ", ";
            os << dep;
            first = false;
        }
        os << "}";
        return os;
    }
    const vector<FuncDep>& getDeps() const { return deps; }
    vector<FuncDep>& getDeps() { return deps; }

    Props CalcClosure(const Props& attrs)
    {
        Props closure = attrs;
        bool changed = true;
        while (changed)
        {
            changed = false;
            for (const auto& dep : getDeps())
            {
                if (dep.getL().is_subset_of(closure) && (changed=closure.insert(dep.getR())))
                {                    
                    break;
                }
            }
        }
        return closure;
    }

    bool IsAttrRightExtranous(        
        vector<FuncDep>::iterator dep_it, 
        vector<char>::const_iterator attr_it)
    {
        // Get the attribute to test
        char attr = *attr_it;
        
        // Determine if the erased element was the first, and capture previous iterator safely
        bool isFirst = (attr_it == dep_it->getR().begin());
        
        // Remove the attribute from the right side
        attr_it=dep_it->getR().erase(attr_it);        
               
        // Calculate closure of left side using the modified system
        Props closure = CalcClosure(dep_it->getL());
        
        // Check if closure contains the attribute
        bool isExtraneous = closure.contains(attr);
        
        dep_it->getR().insert(attr_it, attr);
        
        //cout<<"Testing if attribute "<<attr<<" is right extraneous in dependency "<<*dep_it<<": "<<(isExtraneous ? "Yes" : "No")<<endl;
        return isExtraneous;
    }

    void RemoveRightExtranous()
    {
        bool prev_removed=false;
        for (auto dep_it = getDeps().begin(); 
             dep_it != getDeps().end(); 
             (!prev_removed) ? ++dep_it:dep_it)
        {
            prev_removed=false;
            bool prev_attr_removed=false;
            for (auto attr_it = dep_it->getR().begin(); 
                 attr_it != dep_it->getR().end();
                 (!prev_attr_removed) ? ++attr_it:attr_it)
            {
                prev_attr_removed=false;
                if (IsAttrRightExtranous(dep_it, attr_it))
                {
                    attr_it = dep_it->getR().erase(attr_it);
                    prev_attr_removed=true;
                    if (dep_it->r.data.empty())
                    {
                        dep_it=deps.erase(dep_it);
                        prev_removed=true;
                        break;
                    }
                }
            }
        }
    }

    bool IsAttrLeftExtranous(        
        vector<FuncDep>::iterator dep_it, 
        vector<char>::const_iterator attr_it)
    {
        // Get the attribute to test
        char attr = *attr_it;
        
        // Determine if the erased element was the first, and capture previous iterator safely
        bool isFirst = (attr_it == dep_it->getR().begin());
        
        // Remove the attribute from the right side
        attr_it=dep_it->getL().erase(attr_it);
        
        Props lWithoutAttr = dep_it->getL();

        dep_it->getL().insert(attr_it, attr);
               
        // Calculate closure of left side using the modified system
        Props closure = CalcClosure(lWithoutAttr);
        
        // Check if closure contains the attribute
        bool isExtraneous = dep_it->getR().is_subset_of(closure);        
        //cout<<"Testing if attribute "<<attr<<" is left extraneous in dependency "<<*dep_it<<": "<<(isExtraneous ? "Yes" : "No")<<endl;
        
        return isExtraneous;
    }

    void RemoveLeftExtranous()
    {
        for (auto dep_it = getDeps().begin(); 
             dep_it != getDeps().end(); 
             ++dep_it)
        {
            if(dep_it->getL().data.size()<=1)
                continue;
            for (auto attr_it = dep_it->getL().begin(); 
                 attr_it != dep_it->getL().end();)
            {
                if (IsAttrLeftExtranous(dep_it, attr_it))
                {                    
                    attr_it = dep_it->getL().erase(attr_it);                   
                    if(dep_it->getL().data.size()<=1)
                    {
                        break;
                    }
                }
                else
                {
                    attr_it++;
                }
            }
        }
    }

    bool UniteDepsWithSameLeft()
    {
        bool united=false;
        for (auto dep_it = getDeps().begin(); 
             dep_it != getDeps().end(); 
             ++dep_it)
        {
            for (auto dep_it2 = dep_it+1; 
                 dep_it2 != getDeps().end();)
            {
                //cout<<"Comparing "<<*dep_it<<" and "<<*dep_it2<<endl;
                if (dep_it->getL().is_subset_of(dep_it2->getL()) && dep_it2->getL().is_subset_of(dep_it->getL()))                      
                {
                    dep_it->getR().insert(dep_it2->getR());
                    dep_it2=deps.erase(dep_it2);
                    united=true;                     
                }
                else
                {
                    dep_it2++;
                }              
            }
        }
        return united;
    }

    
    void Canonicalize()
    {
        RemoveRightExtranous();
        RemoveLeftExtranous();        
        if (UniteDepsWithSameLeft())
        {
            RemoveRightExtranous();
        }
    }

    FuncSys CalcProjection(Props s)
    {                
        int n = s.data.size();
        int total = 1 << n;  // 2^n subsets

        vector<FuncDep> projected_deps;
        
        for (int mask = 1; mask < total; ++mask)
        {
            Props subset;
            
            for (int i = 0; i < n; ++i)
            {
                if (mask & (1 << i))
                {
                    subset.insert(s.data[i]);
                }
            }
            Props closure = CalcClosure(subset);
            Props lside = Props(closure - subset).project_onto(s);
            if (!lside.data.empty())
            {      
                projected_deps.push_back(FuncDep(subset, lside));
            }
        }

        FuncSys projected_sys(projected_deps, s);
        projected_sys.Canonicalize();        
        return projected_sys;
    }

    PropsSet CalcKeys()
    {
        int n = set.data.size();
        int total = 1 << n;  // 2^n subsets

        PropsSet keys;
        
        for (int mask = 1; mask < total; ++mask)
        {
            Props subset;
            
            for (int i = 0; i < n; ++i)
            {
                if (mask & (1 << i))
                {
                    subset.insert(set.data[i]);
                }
            }
            Props closure = CalcClosure(subset);
            if (closure == set)
            {      
                if (std::none_of(keys.begin(), keys.end(), [&](const Props& key){ return key.is_subset_of(subset); }))  
                {                    
                    keys.insert(subset);
                }
                else
                {
                    // Remove any existing keys that are supersets of the new key
                    for (auto it = keys.begin(); it != keys.end(); )
                    {
                        if (subset.is_subset_of(*it) && !(subset == *it))
                        {
                            it = keys.erase(it);
                        }
                        else
                        {
                            ++it;
                        }
                    }
                }
            }
        }
        return keys;
    }
};

void checkHW3Q3()
{
    FuncSys fs({"A->DE", "CD->AB", "E->ECG", "BG->AE", "AG->BD"},Props("ABCDEG"));
    fs.Canonicalize();
    cout << fs << endl;
    cout<< "Keys: "<<fs.CalcKeys()<<endl;


    FuncSys fsA = fs.CalcProjection(Props("ECG"));
    FuncSys fsB = fs.CalcProjection(Props("ABD"));
    cout<<"Projection on ABCD: "<<fsA<<" keys"<< fsA.CalcKeys() <<endl;
    cout<<"Projection on CEG: "<<fsB<<" keys"<< fsB.CalcKeys() <<endl;
}

void checkHW3Q4SectionB()
{
    FuncSys fs({"B->G", "EG->BC", "C->ABG", "ABC->E", "DE->B"}, Props("ABCDEG"));
    fs.Canonicalize();
    FuncSys fsA = fs.CalcProjection(Props("ABCD"));
    FuncSys fsB = fs.CalcProjection(Props("CEG"));
    cout << fs << endl;
    cout<< "Keys: "<<fs.CalcKeys()<<endl;
    cout<<"Projection on ABCD: "<<fsA<<" keys"<< fsA.CalcKeys() <<endl;
    cout<<"Projection on CEG: "<<fsB<<" keys"<< fsB.CalcKeys() <<endl;
}

void checkHW3Q4SectionE()
{
    FuncSys fs({"B->G", "EG->BC", "C->ABG", "ABC->E", "DE->B"}, Props("ABCDEG"));
    fs.Canonicalize();
    FuncSys fsA = fs.CalcProjection(Props("BG"));
    FuncSys fsB = fs.CalcProjection(Props("CEG"));
    FuncSys fsC = fs.CalcProjection(Props("CABE"));
    FuncSys fsD = fs.CalcProjection(Props("DEB"));
    cout << fs << endl;
    cout<< "Keys: "<<fs.CalcKeys()<<endl;
    cout<<"Projection on BG: "<<fsA<<" keys"<< fsA.CalcKeys() <<endl;
    cout<<"Projection on CEG: "<<fsB<<" keys"<< fsB.CalcKeys() <<endl;
    cout<<"Projection on CABE: "<<fsC<<" keys"<< fsC.CalcKeys() <<endl;
    cout<<"Projection on DEB: "<<fsD<<" keys"<< fsD.CalcKeys() <<endl;
}

void check1()
{
    FuncSys fs({"C->E", "D->BC", "B->AC"},Props("ABCDE"));
    fs.Canonicalize();
    FuncSys fs1 = fs.CalcProjection(Props("BCE"));
    FuncSys fs2 = fs.CalcProjection(Props("ABD"));
    cout << "Cononized fs" << fs << endl;
    cout<< "Keys: "<<fs.CalcKeys()<<endl;
    cout<<"Projection on BCE: "<<fs1<<" keys"<< fs1.CalcKeys() <<endl;
    cout<<"Projection on ABD: "<<fs2<<" keys"<< fs2.CalcKeys() <<endl;    
}

void year2024A_moed87_q4()
{
    FuncSys fs({"AG-B", "EBD->AC", "E->BG","AG->E","B->A"},Props("ABCDEG"));
    fs.Canonicalize();
    cout << "Cononized fs" << fs << endl;
    cout<< "Keys: "<<fs.CalcKeys()<<endl;
    FuncSys fs1 = fs.CalcProjection(Props("EDC"));
    FuncSys fs2 = fs.CalcProjection(Props("EBG"));
    FuncSys fs3 = fs.CalcProjection(Props("AGE"));
    FuncSys fs4 = fs.CalcProjection(Props("BA"));
    
    cout<<"Projection on EDC: "<<fs1<<" keys"<< fs1.CalcKeys() <<endl;
    cout<<"Projection on EBG: "<<fs2<<" keys"<< fs2.CalcKeys() <<endl;
    cout<<"Projection on AGE: "<<fs3<<" keys"<< fs3.CalcKeys() <<endl;
    cout<<"Projection on BA: "<<fs4<<" keys"<< fs4.CalcKeys() <<endl; 
}


void year2024A_moed61_q4()
{
    FuncSys fs({"AB->CD", "D->BE", "E->C", "DE->G"},Props("ABCDEG"));
    fs.Canonicalize();
    cout << "Cononized fs" << fs << endl;
    cout<< "Keys: "<<fs.CalcKeys()<<endl;
    FuncSys fs1 = fs.CalcProjection(Props("ABD"));
    FuncSys fs2 = fs.CalcProjection(Props("DBEG"));    
    
    cout<<"Projection on ABD: "<<fs1<<" keys"<< fs1.CalcKeys() <<endl;
    cout<<"Projection on DBEG: "<<fs2<<" keys"<< fs2.CalcKeys() <<endl; 
}

/*AB->CD
G->A
BG->E
EC->BG*/

void year2026A_moedA2_q6()
{
    FuncSys fs({"AB->CD","G->A","BG->E","EC->BG"},Props("ABCDEG"));
    fs.Canonicalize();
    cout << "Cononized fs" << fs << endl;
    cout<< "Keys: "<<fs.CalcKeys()<<endl;
    FuncSys fs1 = fs.CalcProjection(Props("ABCD"));
    FuncSys fs2 = fs.CalcProjection(Props("GA"));
    FuncSys fs3 = fs.CalcProjection(Props("ECBG"));    
    
    cout<<"Projection on ABCD: "<<fs1<<" keys"<< fs1.CalcKeys() <<endl;
    cout<<"Projection on GA: "<<fs2<<" keys"<< fs2.CalcKeys() <<endl;
    cout<<"Projection on ECBG: "<<fs3<<" keys"<< fs3.CalcKeys() <<endl; 
}

int main()
{
    year2026A_moedA2_q6();
    return 0;

    FuncDep fd("AB","C");
    cout << fd << endl;
    FuncSys fs({"A->B", "B->C", "AC->D"},Props("ABCD"));
    cout << fs << endl;
    FuncSys fs2({"A->DE", "CD->AB", "E->ECG", "BG->AE", "AG->BD"},Props("ABCDEG"));
    FuncSys fs3=fs2;
    cout << fs2 << endl;
    Props attrs;
    attrs.insert('A');
    Props closure = fs2.CalcClosure(attrs);
    cout << "Closure of A: " << closure << endl;

    fs2.RemoveRightExtranous();
    cout << "After removing right extraneous: " << fs2 << endl;
    
    ostringstream oss;
    oss << fs2;
    assert(oss.str()=="{A->E, CD->A, E->CG, BG->A, AG->BD}");
    

    fs2.IsAttrLeftExtranous(fs2.getDeps().begin(), fs2.getDeps().begin()->getL().begin());
    fs2.RemoveLeftExtranous();
    cout << "After removing left extraneous: " << fs2 << endl;

    fs2.UniteDepsWithSameLeft();
    cout << "After uniting dependencies with same left side: " << fs2 << endl;

    cout<<"Canonicalizing fs3:"<<fs3<< endl;
    fs3.Canonicalize();
    cout << "Canonical form of fs3: " << fs3 << endl;  

    FuncSys fs2A = fs2.CalcProjection(Props("ECG"));
    cout << "Projection on " << Props("ECG") << ": " << fs2A << endl;
    FuncSys fs2B = fs2.CalcProjection(Props("ABDE"));
    cout << "Projection on " << Props("ABDE") << ": " << fs2B << endl;
    cout<<"keys:"<<fs2.CalcKeys();

    return 0;
}