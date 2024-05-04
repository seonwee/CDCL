#include<vector>
#include<string>
#include<iostream>
#include<cstdlib>
#include<deque>
#include<unordered_set>
#include<json.h>
#include<chrono>
#include<array>
#include<algorithm>
using namespace std;
typedef unsigned int uint;
typedef unsigned char uchar;
//ÿ����Ԫ��Ӧ�������֣�һ���Ǳ�Ԫ�����������֣�����һ������񶨣��������֣�
//��lit�������֣����������ֺ͸����֣���var�����Ԫ��lit=var��ʾ�����֣�lit=-var��ʾ������


enum {
	CLAUSE_DEFAULT = 0,
	CLAUSE_LEARNT = 1,
	CLAUSE_LOCK = 2,
};
enum {
	ASSIGNED = 1,
	ASSIGNED_TRUE = 2,
};
struct clause {
	uint num_lit;
	int* lits;//[0]��[1]λ����2WL���ල��������Ԫ
	uint score;
	int flag;
};
const uint UNIT_RUN_FACTOR = 16;
const double DECAY_FACTOR = 0.9;
const double ACTIVITY_RESCALE_LIMIT = 1e100;
uint N;//��Ԫ�ĸ���
uint M;//�Ӿ�ĸ���
vector<vector<int>> F;

vector<vector<clause*>> pos_list, neg_list;//pos_list[i]��ʾ�����ܵ��ල�ı�Ԫi���Ӿ䣬neg_list[i]��ʾ�����ܵ��ල�ı�Ԫ-i���Ӿ�
deque<clause*> clauses;
uint num_clauses;
uint decision_level;//��ǰ�ǵڼ����߲�
vector<int> decision;//decision[i]��ʾ��i���߲�ľ��߱�Ԫ
vector<uint> level;//level[i]��ʾ��Ԫi���ڵĵڼ����߲�
vector<clause*> reason;//reason[i]��ʾ��Ԫi��ֵ�����ĸ��Ӿ��Ƶ�������
vector<int> trail;
vector<double> activity;//EVSIDS���ԣ�activity[i]��ʾ��Ԫi�ĵ÷֣���ʼΪ0
vector<uint> heap;//priority queue��heap[1]�ǶѶ�Ԫ�أ�heap[0]��ʹ��
vector<uint> heap_idx;//heap_idx[i]��ʾ��Ԫi��heap�е��±꣬��ֵ0��ʾ��Ԫi����heap��
vector<uchar> assign;//assign[i]��ʾ��Ԫi�ĸ�ֵ������Լ���¼��Ԫi��һ�θ�ֵ�����
vector<int> learn_clause;//ֻ��analyze_conflict��ʹ�ã����ڴ洢��ͻ֮��ѧϰ�����Ӿ�
vector<bool> visited;//ֻ��analyze_conflict��ʹ�ã����ڱ�Ǳ�Ԫ�Ƿ񱻷��ʹ�
//unordered_set<uint> calculate_lbd;//ֻ��update_clause_score��ʹ�ã����ڼ����Ӿ��LBDֵ
vector<bool> visited_level;//ֻ��update_clause_score��ʹ�ã����ڼ����Ӿ��LBDֵ
uint count_reduce;//ָ�˴��Ӿ�ɾ��֮ǰ�Ѿ�ִ�е��Ӿ�ɾ���Ĵ���
uint total_conflict;//�ܹ���ͻ����
uint count_restart;//��������
uint luby_idx;
uint threshold_value_restart;//����timer_restart��ֵ�ж��Ƿ�ﵽ������ֵ
uint timer_restart;
uint count_simplify;
array<int, 2> luby_seq{ 1, 1 };
double activity_increment = 1.0;
bool is_assigned(uint var) {
	return assign[var] & ASSIGNED;
}
/**
 * @brief �жϱ�Ԫvar֮ǰ�Ƿ��б�����ֵ����
 * @param var
 */
bool is_last_assigned_true(uint var) {
	return assign[var] & ASSIGNED_TRUE;
}
int ev(uint var) {//ev = evaluate value
	return is_assigned(var) ? ((assign[var] & ASSIGNED_TRUE) ? var : -(int)var) : 0;
}
bool heap_compare_gt(uint i, uint j) {
	return activity[heap[i]] > activity[heap[j]];
}
bool heap_empty() {
	return heap.size() == 1;
}
void heap_swap(uint i, uint j) {
	heap_idx[heap[i]] = j;
	heap_idx[heap[j]] = i;
	swap(heap[i], heap[j]);
}
uint heap_up(uint i) {
	uint parent;
	while ((parent = i >> 1) && heap_compare_gt(i, parent)) {
		heap_swap(i, parent);
		i = parent;
	}
	return i;
}
uint heap_down(uint i) {
	uint lchild = i << 1;
	uint rchild = lchild + 1;
	uint max_idx = i;
	if (lchild < heap.size() && heap_compare_gt(lchild, max_idx)) {
		max_idx = lchild;
	}
	if (rchild < heap.size() && heap_compare_gt(rchild, max_idx)) {
		max_idx = rchild;
	}
	if (max_idx != i) {
		heap_swap(i, max_idx);
		return heap_down(max_idx);
	}
	else return i;
}


void heap_push(uint var) {
	heap.push_back(var);
	heap_idx[var] = heap.size() - 1;
	heap_up(heap.size() - 1);
}
uint heap_top() {
	if (heap_empty()) return 0;
	return heap[1];
}
void heap_pop() {
	uint v = heap_top();
	if (v == 0) return;
	heap_swap(1, heap.size() - 1);
	heap_idx[v] = 0;
	heap.pop_back();
	heap_down(1);
}



clause* make_clause(const vector<int>& lits, uint score, int flag) {
	clause* c = new clause;
	c->num_lit = lits.size();
	c->lits = new int[c->num_lit];
	for (int i = 0; i < c->num_lit; i++) {
		c->lits[i] = lits[i];
	}
	c->score = score;
	c->flag = flag;
	return c;
}

vector<clause*>& get_watch_list(int lit) {
	return lit > 0 ? pos_list[lit] : neg_list[abs(lit)];
}


void watch_clause(clause* c) {
	for (int i = 0; i < 2 && i < c->num_lit; i++) {
		get_watch_list(c->lits[i]).push_back(c);
	}
}

void unwatch_clause(clause* c) {
	for (int i = 0; i < c->num_lit && i < 2; i++) {
		vector<clause*>& list = get_watch_list(c->lits[i]);
		for (int j = 0; j < list.size(); j++) {
			if (list[j] == c) {
				list[j] = list.back();
				list.pop_back();
				break;
			}
		}
	}
}

void readCNF(string cnfFileName) {
	FILE* cnfFile;
	if (freopen_s(&cnfFile, cnfFileName.c_str(), "r", stdin) != 0) {
		cout << "CNF File not found!" << endl;
		exit(EXIT_FAILURE);
	}
	while (getchar() == 'c') {
		while (getchar() != '\n');
	}
	scanf_s(" cnf %d %d", &N, &M);
	F.resize(M);
	//activity.resize(N + 1);
	for (vector<int>& c : F) {
		int lit;
		while (scanf_s("%d", &lit), lit != 0) {
			c.push_back(lit);
			//activity[abs(lit)]++;
		}
	}
}
void push_trail(int lit, clause* c) {
	uint var = abs(lit);
	trail.push_back(lit);
	assign[var] = lit > 0 ? (ASSIGNED | ASSIGNED_TRUE) : ASSIGNED;
	level[var] = decision_level;
	reason[var] = c;
	if (c) {
		c->flag |= CLAUSE_LOCK;
	}
}
void pop_trail() {
	int lit = trail.back();
	trail.pop_back();
	uint var = abs(lit);
	assign[var] &= ~ASSIGNED;
	level[var] = 0;
	clause* c = reason[var];
	if (c) {
		c->flag &= ~CLAUSE_LOCK;
	}
	reason[var] = nullptr;
	if (heap_idx[var] == 0) heap_push(var);
}
/**
 * @brief ͨ��LBD�Ʒֲ��Լ����Ӿ�c�ĵ÷�
 * @param c
 */
void update_clause_score(clause* c) {
	uint lbd_score = 0;
	for (int i = 0; i < c->num_lit; i++) {
		uint lv = level[abs(c->lits[i])];
		if (!visited_level[lv]) {
			lbd_score++;
			visited_level[lv] = true;
		}
	}
	c->score = lbd_score;
	for (int i = 0; i < c->num_lit; i++) {
		visited_level[level[abs(c->lits[i])]] = false;
	}
}
clause* unit_propagate() {
	for (int i = trail.size() - 1; i < trail.size(); i++) {
		int lit = trail[i];
		vector<clause*>& wl = get_watch_list(-lit);
		for (int j = 0; j < wl.size(); j++) {
			clause* c = wl[j];
			if (c->lits[0] == -lit)
				swap(c->lits[0], c->lits[1]);
			if (ev(abs(c->lits[0])) == c->lits[0]) continue;//�Ӿ�c�Ѿ�����
			bool not_find = true;
			for (int k = 2; k < c->num_lit; k++) {//�ҵ���һ�����Լල������
				int literal = c->lits[k];
				if (ev(abs(literal)) != -literal) {
					swap(c->lits[1], c->lits[k]);
					get_watch_list(literal).push_back(c);//�����ҵ��ļල���ֽ��мල
					wl[j] = wl.back();//ȡ����֮ǰ���ֵļල
					wl.pop_back();
					j--;
					not_find = false;
					break;
				}
			}
			if (not_find) {
				if (is_assigned(abs(c->lits[0]))) {
					return c;//���ֳ�ͻ�����س�ͻ�Ӿ�
				}
				else {
					push_trail(c->lits[0], c);
					update_clause_score(c);
				}
			}
		}
	}
	return nullptr;//û�г�ͻ
}

void update_activity(uint var) {
	activity[var] += activity_increment;
	if (activity[var] > ACTIVITY_RESCALE_LIMIT) {
		activity_increment *= (1.0 / ACTIVITY_RESCALE_LIMIT);
		for (uint v = 1; v <= N; ++v)
			activity[v] *= (1.0 / ACTIVITY_RESCALE_LIMIT);
	}
	if (heap_idx[var]) {
		heap_up(heap_idx[var]);
	}
}
inline void update_activity_increment() {
	activity_increment *= (1.0 / DECAY_FACTOR);
}
uint get_back_level() {
	uint back_level = 0;
	for (int i = 1; i < learn_clause.size(); i++) {
		back_level = max(back_level, level[abs(learn_clause[i])]);
	}
	return back_level;
}

void backjump(uint back_level) {
	while (decision_level != back_level) {
		while (trail.back() != 0) pop_trail();
		trail.pop_back();//�Ƴ����߱�Ԫ���0
		decision_level--;
	}
}

void analyze_conflict(clause* conflict) {

	uint count = 0;//�Ӻ���ǰ����������¼���л�ʣ���ٸ�>=decision_level�ı�Ԫ
	int uip = 0;
	learn_clause.push_back(0);
	/*cout << "conflict_clause:" << endl;
	for (int i = 0; i < conflict->num_lit; i++) {
		cout << conflict->lits[i] << "@" << level[abs(conflict->lits[i])] << " ";
	}
	cout << endl;
	cout << "reason[var]:" << endl;
	for (int i = 0; i < trail.size(); i++) {
		if (trail[i] == 0) continue;
		clause* c = reason[abs(trail[i])];
		cout << "reason[" << abs(trail[i]) << "@" << level[abs(trail[i])] << "] = ";
		if (c) {
			for (int i = 0; i < c->num_lit; i++) {
				cout << c->lits[i] << "@" << level[abs(c->lits[i])] << " ";
			}
		}
		cout << endl;
	}
	cout << "trail <-> level" << endl;
	for (int i = 0; i < trail.size(); i++) {
		if (trail[i] == 0) continue;
		cout << trail[i] << " <-> " << level[abs(trail[i])] << endl;
	}*/
	for (int i = 0; i < conflict->num_lit; i++) {
		int lit = conflict->lits[i];
		uint var = abs(lit);
		uint lv = level[var];
		if (lv == 0) continue;
		visited[var] = true;
		if (lv < decision_level) {
			learn_clause.push_back(lit);
		}
		else {
			count++;
		}
		update_activity(var);
	}
	for (int i = trail.size() - 1; i >= 0; i--) {
		int lit = trail[i];
		uint var = abs(lit);
		if (!visited[var]) continue;
		visited[var] = false;
		count--;
		if (count == 0) {
			uip = lit;
			break;
		}
		clause* c = reason[var];
		if (c) {
			for (uint j = 0; j < c->num_lit; j++) {
				int l = c->lits[j];
				uint v = abs(l);
				uint lv = level[v];
				if (visited[v] || lv == 0 || l == lit) continue;
				visited[v] = true;
				if (lv < decision_level) {
					learn_clause.push_back(l);
				}
				else {
					count++;
				}
				update_activity(v);
			}

		}
	}
	learn_clause[0] = -uip;

	/*cout << "learn_clause:" << endl;
	for (const int& lit : learn_clause) {
		cout << lit << " ";
	}
	cout << endl;*/

	for (int i = 1; i < learn_clause.size(); i++) {
		visited[abs(learn_clause[i])] = false;
	}
	/*for (bool b : visited) {
		if (b) {
			cout << "has true not clear" << endl;
		}
	}*/
	uint back_level = get_back_level();
	backjump(back_level);
	if (learn_clause.size() == 1) {
		push_trail(-uip, nullptr);
	}
	else {
		clause* c = make_clause(learn_clause, 0, CLAUSE_LEARNT);
		push_trail(-uip, c);
		update_clause_score(c);
		if (c->num_lit == 2 || c->score <= 2)
		{
			clauses.push_front(c);
			num_clauses++;
		}
		else {
			clauses.push_back(c);
		}
		watch_clause(c);
	}
	learn_clause.clear();
}
int choose() {
	while (!heap_empty()) {
		if (heap[0] != 0) cout << "heap[0] is not zero!" << endl;
		uint var = heap_top();
		heap_pop();
		if (!is_assigned(var)) {
			return is_last_assigned_true(var) ? var : -int(var);
		}
	}
	return 0;
}

/**
 * @brief ѡȡ���߱�Ԫ����ִ�о���
 * @return ���߳ɹ�����true�����򷵻�false(��heapΪ�գ����еı�Ԫ�Ѿ�����ֵ��û�����ɱ�Ԫ���Խ��о��ߵ����)��
 */
bool decide() {
	int decision_lit = choose();
	if (decision_lit == 0) return false;
	decision_level++;
	decision[decision_level] = decision_lit;
	trail.push_back(0);
	push_trail(decision_lit, nullptr);
	return true;
}
void reduce() {
	if (total_conflict < 20000 + 500 * count_reduce) return;
	count_reduce++;
	sort(next(clauses.begin(), num_clauses), clauses.end(), [](const clause* c1, const clause* c2) {
		return c1->score < c2->score;
		});
	uint new_size = num_clauses + ((clauses.size() - num_clauses) >> 1);
	for (int i = new_size; i < clauses.size(); i++) {
		clause* c = clauses[i];
		if ((c->flag & CLAUSE_LEARNT) && (c->flag & CLAUSE_LOCK)) {
			clauses[new_size++] = c;
			continue;
		}
		unwatch_clause(c);
		delete[] c->lits;
		delete c;
	}
	clauses.resize(new_size);
}
int luby() {
	luby_seq = {
		(luby_seq[0] & -luby_seq[0]) == luby_seq[1] ? luby_seq[0] + 1 : luby_seq[0],
		(luby_seq[0] & -luby_seq[0]) == luby_seq[1] ? 1 : 2 * luby_seq[1]
			};
	return luby_seq[1];
}
void restart() {
	if (timer_restart < threshold_value_restart) return;
	count_restart++;
	threshold_value_restart = luby() * UNIT_RUN_FACTOR;
	timer_restart = 0;
	backjump(0);
}
void simplify() {
	if (decision_level > 0) return;
	count_simplify++;
	uint new_size = 0;
	for (uint i = 0; i < clauses.size(); i++) {
		clause* c = clauses[i];
		bool satisfiable = false;
		uint new_num_lit = 0;
		for (uint j = 0; j < c->num_lit; j++) {
			int lit = c->lits[j];
			uint var = abs(lit);
			if (!is_assigned(var)) {
				c->lits[new_num_lit++] = lit;
			}
			else {
				if (ev(var) == lit) {
					satisfiable = true;
					break;
				}
			}
		}
		if (satisfiable) {
			unwatch_clause(c);
			delete[] c->lits;
			delete c;
		}
		else {
			c->num_lit = new_num_lit;
			clauses[new_size++] = c;
		}
	}
	clauses.resize(new_size);
	num_clauses = new_size;
}

bool solve() {
	//initialize
	pos_list.resize(N + 1);
	neg_list.resize(N + 1);
	decision_level = 0;
	decision.resize(N + 1);//[0]λ�ò�ʹ�ã�decision[1]��ʾ��һ���߲�ľ��߱�Ԫ���Դ�����
	level.resize(N + 1);
	reason.resize(N + 1);
	trail.reserve(2 * N);//һ����N����Ԫ�����ÿ����Ԫ���Ǿ��߱�Ԫ�����Ͼ��߱��0����ô������󳤶�Ϊ2N
	activity.resize(N + 1);
	heap.push_back(0);//heap[0]��ʹ�ã����ȷ���һ��ռλԪ��0
	heap.reserve(N + 1);
	heap_idx.resize(N + 1);
	assign.resize(N + 1);
	learn_clause.reserve(N);
	visited.resize(N + 1, false);
	//calculate_lbd.reserve(N);
	visited_level.resize(N + 1, false);
	count_reduce = 0;
	total_conflict = 0;
	count_restart = 0;
	luby_idx = 0;
	threshold_value_restart = UNIT_RUN_FACTOR;
	timer_restart = 0;
	count_simplify = 0;
	for (uint i = 1; i <= N; i++) {
		heap_push(i);
	}
	vector<int> unit;
	vector<int> new_lits;
	for (vector<int>& lits : F) {
		size_t size = lits.size();
		if (size == 0) {
			cout << "�����г��ֿ��Ӿ�" << endl;
			exit(EXIT_FAILURE);
		}
		else if (size == 1) {
			unit.push_back(lits[0]);
		}
		else {
			bool tautology = false;
			bool last = true;
			for (int i = 0; i < size; i++) {
				for (int j = i + 1; j < size; j++) {
					if (lits[j] == lits[i]) {
						last = false;
						break;
					}
					if (lits[j] == -lits[i]) {
						tautology = true;
						break;
					}
				}
				if (tautology) break;
				if (last) new_lits.push_back(lits[i]);
			}
			if (tautology) {
				new_lits.clear();
				continue;
			}
			else {
				clause* c = make_clause(new_lits, 0, CLAUSE_DEFAULT);
				clauses.push_back(c);
				watch_clause(c);
				num_clauses++;
				new_lits.clear();
			}
		}
	}
	for (int lit : unit) {
		push_trail(lit, nullptr);
		if (unit_propagate()) {
			return false;
		}
	}
	simplify();
	if (trail.empty() && !decide()) return true;
	uint timer_decay = 0;
	while (true) {
		clause* conflict;
		while ((conflict = unit_propagate())) {
			if (decision_level == 0) {
				return false;//��0���߲������ͻ����������unsat������false
			}
			analyze_conflict(conflict);
			timer_decay++;
			total_conflict++;
			timer_restart++;
			update_activity_increment();
			if (timer_decay == 800) {
				timer_decay = 0;
				for (int i = 1; i < activity.size(); i++) {
					activity[i] = static_cast<int>(static_cast<double>(activity[i]) * DECAY_FACTOR);
					//activity[i] = activity[i] >> 1;
				}
			}			
		}
		restart();
		if (!decide()) return true;
		reduce();
	}
}
std::string toString(const Json::Value& val) {
	static Json::Value def = []() {
		Json::Value def;
		Json::StreamWriterBuilder::setDefaults(&def);
		def["emitUTF8"] = true;
		return def;
		}();
		std::ostringstream stream;
		Json::StreamWriterBuilder stream_builder;
		stream_builder.settings_ = def;//Config emitUTF8
		std::unique_ptr<Json::StreamWriter> writer(stream_builder.newStreamWriter());
		writer->write(val, &stream);
		return stream.str();
}
int main(int argc, char* argv[]) {
	//string cnfFileName = "D:/SAT/instances/Beijing/2bitadd_10.cnf";
	string cnfFileName = argv[1];
	readCNF(cnfFileName);
	auto start = chrono::high_resolution_clock::now();
	bool result = solve();
	auto stop = chrono::high_resolution_clock::now();
	auto duration = chrono::duration_cast<chrono::milliseconds>(stop - start);
	double time = duration.count() / 1000.0;
	Json::Value root;
	double max_num = 0;
	for (double& num : activity) {
		max_num = max(max_num, num);
	}
	root["instance"] = cnfFileName;
	root["time"] = time;
	root["result"] = result ? "SAT" : "UNSAT";
	root["max_activity"] = max_num;
	root["total_conflict"] = total_conflict;
	root["count_reduce"] = count_reduce;
	root["threshold_value_restart"] = threshold_value_restart;
	root["count_simplify"] = count_simplify;
	root["count_restart"] = count_restart;
	cout << "over" << endl;
	cout << root.toStyledString();
}