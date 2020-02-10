// #pragma GCC optimize("O3")
#include <algorithm>
#include <array>
#include <bitset>
#include <cassert>
#include <cfloat>
#include <climits>
#include <cmath>
#include <cstdio>
#include <deque>
#include <iomanip>
#include <iostream>
#include <map>
#include <numeric>
#include <queue>
#include <set>
#include <sstream>
#include <stack>
#include <stdexcept>
#include <unordered_map>
#include <unordered_set>
#include <vector>
using namespace std;

template <class T1, class T2>
ostream& operator << (ostream& out, pair <T1, T2> p)
{
	out << '(' << p.first << ',' << p.second << ')';
	return out;
}

template <class T1, class T2>
istream& operator >> (istream& in, pair<T1, T2> &p)
{
	in >> p.first >> p.second;
	return in;
}

template <class T>
istream& operator >> (istream& in, vector<T> &v)
{
	for (T &x : v)
		in >> x;
	return in;
}

template <class T>
ostream& operator << (ostream& out, vector<vector<T>> &v)
{
	for (vector<T> &x : v)
		out << x << '\n';
	return out;
}

template <class T>
ostream& operator << (ostream& out, vector<T> &v)
{
	for (T &x : v)
		out << x << ' ';
	return out;
}

long long gcd (long long a, long long b)
{
	if (b > a)
		swap(a, b);
	return (b ? gcd(b, a % b) : a);
}

using ll   = long long;
using pii  = pair<int, int>;
using pll  = pair<long long, long long>;
using tiii = pair<pair<int, int>, int>;
using vi   = vector<int>;
using vl   = vector<long long>;
using vvi  = vector<vector<int>>;
using vvl  = vector<vector<long long>>;

#define F          first
#define S          second
#define First      first.first
#define Second     first.second
#define Third      second
#define mp         make_pair
#define rep(i,a,b) for (int i = a; i < b; i++)
#define per(i,b,a) for (int i = b; i > a; i--)
#define all(x)     x.begin(), x.end()
#define ret(x)     return cout << x, 0;
#define throwex    throw runtime_error ("Found the error.");

const int h = 1000000007;

long long p (long long x, long long y)
{
	static const int mod = 998244353;
	if (y == 0) return 1;
	long long z = p (x, y / 2);
	z *= z;
	z %= mod;
	return (y & 1 ? (z * x) % mod : z);
}

long long inv (long long x)
{
	static const int mod = 998244353;
	return p (x, mod - 2);
}

const int mod = 998244353;

class NTT
{
private:
	static const int mod = 998244353;     // 2^23 * 7 * 17 + 1
	static const int root_pw = 1 << 20;
	static const int root = 565042129;    // 3^(8*7*17) modulo mod
	static const int root_1 = 950391366;  // root^-1 modulo mod

	static array<array<long long, root_pw>, 2> wlen_power_arranged;

	static struct StaticConstructor
	{
		StaticConstructor()
		{
			wlen_power_arranged[0][root_pw / 2] = 1;
			wlen_power_arranged[1][root_pw / 2] = 1;
			for (int i = root_pw / 2 + 1; i < root_pw; i++)
			{
				wlen_power_arranged[0][i] = wlen_power_arranged[0][i - 1] * root % mod;
				wlen_power_arranged[1][i] = wlen_power_arranged[1][i - 1] * root_1 % mod;
			}
			for (int i = root_pw / 2 - 1; i > -1; i--)
			{
				wlen_power_arranged[0][i] = wlen_power_arranged[0][2 * i];
				wlen_power_arranged[1][i] = wlen_power_arranged[1][2 * i];
			}
		}
	} static_constructor;

	static long long p (long long x, long long y)
	{
		if (y == 0) return 1;
		long long z = p (x, y / 2);
		z *= z;
		z %= mod;
		return (y & 1 ? (z * x) % mod : z);
	}

	static long long inv (long long x)
	{
		return p (x, mod - 2);
	}

	static void ntt (vector<int> & a, bool invert)
	{
		int n = a.size();
		for(int i=0, j=0; i<n; ++i) {
			if(i>j)
				swap(a[i], a[j]);
			for(int k=n/2; (j^=k)<k; k/=2);
		}

		for (int len = 2; len <= n; len <<= 1) {
			for (int i = 0; i < n; i += len) {
				for (int j = 0; j < len / 2; j++) {
					int u = a[i+j], v = a[i+j+len/2] * wlen_power_arranged[invert][len / 2 + j] % mod;
					a[i+j] = u + v < mod ? u + v : u + v - mod;
					a[i+j+len/2] = u - v >= 0 ? u - v : u - v + mod;
				}
			}
		}

		if (invert) {
			long long n_1 = inv(n);
			for (int & x : a)
				x = x * n_1 % mod;
		}
	}

public:
	static vector<int> multiply(vector<int> const& a, vector<int> const& b)
	{
		vector<int> fa(a.begin(), a.end()), fb(b.begin(), b.end());
		int n = 1;
		while (n < a.size() + b.size() - 1)
			n <<= 1;
		fa.resize(n);
		fb.resize(n);

		ntt(fa, false);
		ntt(fb, false);
		for (int i = 0; i < n; i++)
			fa[i] = (1LL * fa[i] * fb[i] % mod);
		ntt(fa, true);

		while(fa.back() == 0)
			fa.pop_back();

		return fa;
	}
};
array<array<long long, NTT::root_pw>, 2> NTT::wlen_power_arranged;
NTT::StaticConstructor NTT::static_constructor;

array<long long, 1000001> fact, ifact;

// product from 0 to n-1
vi find_product(int n)
{
	if(n == 0)
		return {1};
	vi poly1 = find_product(n / 2);
	poly1.resize(n / 2 + 1);
	vi poly_alpha(n / 2 + 1), poly_beta(n / 2 + 1);
	ll power = 1;
	rep(i, 0, n / 2 + 1)
	{
		poly_alpha[i] = power * ifact[i] % mod;
		poly_beta[i] = poly1[n / 2 - i] * fact[n / 2 - i] % mod;
		power = power * (mod - n / 2) % mod;
	}
	vi poly2 = NTT::multiply(poly_alpha, poly_beta);
	poly2.resize(n / 2 + 1);
	reverse(all(poly2));
	rep(i, 0, n / 2 + 1)
		poly2[i] = poly2[i] * ifact[i] % mod;
	vi poly = NTT::multiply(poly1, poly2);
	poly.resize(2 * (n / 2) + 1);
	if(n & 1)
	{
		poly.insert(poly.begin(), 0);
		rep(i, 0, n)
			poly[i] = (poly[i] + (mod - (n - 1LL)) * poly[i+1]) % mod;
	}
	return poly;
}

signed main()
{
	ios::sync_with_stdio(false);
	#ifdef ONLINE_JUDGE
	cin.tie(nullptr);
	cout.tie(nullptr);
	cerr.setstate(ios::failbit);
	#endif

	fact[0] = 1;
	rep(i, 1, 1000001)
		fact[i] = fact[i-1] * i % mod;
	rep(i, 0, 1000001)
		ifact[i] = inv(fact[i]);

	int t;
	cin >> t;
	while(t--)
	{
		int N, P, R;
		cin >> N >> P >> R;
		vi poly = find_product(R);
		ll ans = 0;
		ll x = 1, pn = p(P, N+1), pin = 1;
		rep(i, 0, poly.size())
		{
			ll partial_ans = poly[i];
			if(x==1)
			{
				partial_ans *= N+1;
				partial_ans %= mod;
			}
			else
			{
				partial_ans *= pin - 1 + mod;
				partial_ans %= mod;
				partial_ans *= inv(x - 1);
				partial_ans %= mod;
			}
			ans += partial_ans;
			ans %= mod;

			x *= P;
			x %= mod;
			pin *= pn;
			pin %= mod;
		}
		ans *= ifact[R];
		ans %= mod;
		cout << ans << '\n';
	}
}
