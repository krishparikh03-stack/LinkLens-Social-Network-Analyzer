/*
  LINKLENS - Social Network Connection Analyzer
  DSA mini-project in C (C99) for Code::Blocks.

  Main concepts: Graph (friendships), Hash Table (username lookup),
  Queue + BFS (shortest connection), and friends-of-friends suggestions.
  Works offline with a fictional demo network or profiles created by users.
*/
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <errno.h>
#include <limits.h>
#include <stdint.h>

#define MAX_USERS 256
#define HASH_SIZE 1031
#define HANDLE_LEN 20
#define NAME_LEN 40
#define CITY_LEN 30
#define LINE_LEN 512
#define MAX_RESULTS 10
#define SAVE_FILE "linklens_network.sna"
#define BACKUP_FILE "linklens_network.bak"
#define TEMP_FILE "linklens_network.tmp"
/* The example and personal networks are saved separately. */
#define DEMO_SAVE_FILE "linklens_demo.sna"
#define DEMO_BACKUP_FILE "linklens_demo.bak"
#define DEMO_TEMP_FILE "linklens_demo.tmp"

static int demoMode = 0;

static const char *interestNames[8] = {
    "Technology", "Sports", "Music", "Travel", "Fitness", "Reading", "Gaming", "Art"
};

typedef struct {
    int *v;
    int count;
    int capacity;
} Neighbors;

typedef struct {
    unsigned id;
    char handle[HANDLE_LEN + 1];
    char name[NAME_LEN + 1];
    char city[CITY_LEN + 1];
    unsigned interests;
    int discoverable;
    int active;
} Profile;

typedef struct {
    char key[HANDLE_LEN + 1];
    int index;
    unsigned char state; /* 0 empty, 1 in use, 2 tombstone */
} HashEntry;

typedef struct {
    Profile profiles[MAX_USERS];
    Neighbors adjacent[MAX_USERS];
    HashEntry lookup[HASH_SIZE];
    unsigned nextId;
    int userCount;
    int friendshipCount;
    int dirty;
} Network;

typedef struct {
    int data[MAX_USERS];
    int front, rear, count;
} Queue;

typedef struct {
    int index;
    int mutual;
    int shared;
    int sameCity;
    int score;
} Recommendation;



static void divider(void) {
    puts("----------------------------------------------------------------------------");
}

static void banner(const char *text) {
    putchar('\n'); divider(); printf("  %s\n", text); divider();
}

static void trim(char *s) {
    size_t n = strlen(s);
    size_t first = 0;
    while (first < n && isspace((unsigned char)s[first])) first++;
    if (first) memmove(s, s + first, n - first + 1);
    n = strlen(s);
    while (n && isspace((unsigned char)s[n - 1])) s[--n] = '\0';
}

/* Returns 0 on end-of-input; strips overlong lines rather than truncating. */
static int inputLine(const char *prompt, char *out, size_t capacity) {
    char line[LINE_LEN];
    size_t n;
    if (prompt) { fputs(prompt, stdout); fflush(stdout); }
    if (!fgets(line, sizeof(line), stdin)) return 0;
    n = strlen(line);
    if (n && line[n - 1] == '\n') line[--n] = '\0';
    else if (!feof(stdin)) {
        int ch;
        while ((ch = getchar()) != '\n' && ch != EOF) { }
        if (n == sizeof(line) - 1) { puts("  [!] Input too long."); out[0] = '\0'; return 1; }
    }
    if (n && line[n - 1] == '\r') line[--n] = '\0';
    trim(line);
    if (strlen(line) >= capacity) {
        printf("  [!] Maximum length is %lu characters.\n", (unsigned long)(capacity - 1));
        out[0] = '\0'; return 1;
    }
    strcpy(out, line);
    return 1;
}

/* Keep results visible until the user is ready to return to the menu. */
static void waitForEnter(void) {
    char unused[LINE_LEN];
    (void)inputLine("\n  Press ENTER to return to the menu...", unused, sizeof(unused));
}

static int parseUnsigned(const char *s, unsigned *result) {
    char *end;
    unsigned long x;
    if (!s || !*s || s[0] == '-' || s[0] == '+') return 0;
    errno = 0;
    x = strtoul(s, &end, 10);
    if (errno || *end || x > UINT_MAX) return 0;
    *result = (unsigned)x;
    return 1;
}

static int choose(const char *prompt, int min, int max) {
    char s[64]; unsigned number;
    for (;;) {
        if (!inputLine(prompt, s, sizeof(s))) return -1;
        if (parseUnsigned(s, &number) && number >= (unsigned)min && number <= (unsigned)max)
            return (int)number;
        printf("  [!] Enter a whole number between %d and %d.\n", min, max);
    }
}

static int validHandle(const char *s) {
    size_t i, n = strlen(s);
    if (n < 3 || n > HANDLE_LEN || !(s[0] >= 'a' && s[0] <= 'z')) return 0;
    for (i = 0; i < n; i++)
        if (!((s[i] >= 'a' && s[i] <= 'z') || (s[i] >= '0' && s[i] <= '9') || s[i] == '_')) return 0;
    return 1;
}

static void normalizeHandle(char *s) {
    size_t i;
    if (*s == '@') memmove(s, s + 1, strlen(s));
    for (i = 0; s[i]; i++) s[i] = (char)tolower((unsigned char)s[i]);
}

static int sameCity(const char *a, const char *b) {
    while (*a && *b) {
        if (tolower((unsigned char)*a) != tolower((unsigned char)*b)) return 0;
        a++; b++;
    }
    return !*a && !*b;
}

/* Keep serialized profile fields printable, delimited safely, and single-line. */
static int validText(const char *s, size_t maximum) {
    size_t i, n = strlen(s);
    if (!n || n > maximum) return 0;
    for (i = 0; i < n; i++) {
        unsigned char ch = (unsigned char)s[i];
        if (ch < 32 || ch > 126 || ch == '|') return 0;
    }
    return 1;
}

static int promptText(const char *prompt, char *out, size_t capacity) {
    for (;;) {
        if (!inputLine(prompt, out, capacity)) return 0;
        if (validText(out, capacity - 1)) return 1;
        puts("  [!] Enter a nonempty, printable value without '|'.");
    }
}

static unsigned hashKey(const char *s) {
    uint32_t h = UINT32_C(2166136261);
    while (*s) { h ^= (unsigned char)*s++; h *= UINT32_C(16777619); }
    return (unsigned)(h % HASH_SIZE);
}

static int mapGet(const Network *n, const char *key) {
    unsigned start = hashKey(key), step;
    for (step = 0; step < HASH_SIZE; step++) {
        const HashEntry *entry = &n->lookup[(start + step) % HASH_SIZE];
        if (!entry->state) return -1;
        if (entry->state == 1 && strcmp(entry->key, key) == 0) return entry->index;
    }
    return -1;
}

static int mapPut(Network *n, const char *key, int index) {
    unsigned start = hashKey(key), step;
    int target = -1;
    for (step = 0; step < HASH_SIZE; step++) {
        HashEntry *entry = &n->lookup[(start + step) % HASH_SIZE];
        if (entry->state == 1 && strcmp(entry->key, key) == 0) return 0;
        if (entry->state == 2 && target == -1) target = (int)((start + step) % HASH_SIZE);
        if (entry->state == 0) {
            if (target == -1) target = (int)((start + step) % HASH_SIZE);
            break;
        }
    }
    if (target < 0) return 0;
    strcpy(n->lookup[target].key, key);
    n->lookup[target].index = index;
    n->lookup[target].state = 1;
    return 1;
}

static void mapDelete(Network *n, const char *key) {
    unsigned start = hashKey(key), step;
    for (step = 0; step < HASH_SIZE; step++) {
        HashEntry *entry = &n->lookup[(start + step) % HASH_SIZE];
        if (entry->state == 0) return;
        if (entry->state == 1 && strcmp(entry->key, key) == 0) {
            entry->state = 2; return;
        }
    }
}

static void initNetwork(Network *n) {
    memset(n, 0, sizeof(*n));
    n->nextId = 1001;
}

static void clearNetwork(Network *n) {
    int i;
    for (i = 0; i < MAX_USERS; i++) {
        free(n->adjacent[i].v);
        n->adjacent[i].v = NULL;
        n->adjacent[i].count = n->adjacent[i].capacity = 0;
    }
    initNetwork(n);
}

static int findId(const Network *n, unsigned id) {
    int i;
    for (i = 0; i < MAX_USERS; i++)
        if (n->profiles[i].active && n->profiles[i].id == id) return i;
    return -1;
}

static int registerProfile(Network *n, unsigned id, const char *handle,
                           const char *name, const char *city, unsigned interests,
                           int discoverable) {
    int i;
    if (n->userCount >= MAX_USERS || !id || !validHandle(handle) ||
        !validText(name, NAME_LEN) || !validText(city, CITY_LEN) ||
        (interests & ~255u) || (discoverable != 0 && discoverable != 1) ||
        mapGet(n, handle) >= 0 || findId(n, id) >= 0) return -1;
    for (i = 0; i < MAX_USERS; i++) if (!n->profiles[i].active) break;
    if (i == MAX_USERS || !mapPut(n, handle, i)) return -1;
    n->profiles[i].id = id;
    strcpy(n->profiles[i].handle, handle);
    strcpy(n->profiles[i].name, name);
    strcpy(n->profiles[i].city, city);
    n->profiles[i].interests = interests;
    n->profiles[i].discoverable = discoverable;
    n->profiles[i].active = 1;
    n->userCount++;
    return i;
}

static int hasFriend(const Network *n, int a, int b) {
    int i;
    for (i = 0; i < n->adjacent[a].count; i++)
        if (n->adjacent[a].v[i] == b) return 1;
    return 0;
}

static int reserveNeighbor(Neighbors *list, int wanted) {
    int capacity;
    int *newData;
    if (wanted <= list->capacity) return 1;
    capacity = list->capacity ? list->capacity * 2 : 4;
    while (capacity < wanted) capacity *= 2;
    newData = (int *)realloc(list->v, (size_t)capacity * sizeof(int));
    if (!newData) return 0;
    list->v = newData;
    list->capacity = capacity;
    return 1;
}

/* Status: 1 inserted; 0 duplicate/self/invalid; -1 allocation failure. */
static int connectProfiles(Network *n, int a, int b) {
    if (a < 0 || a >= MAX_USERS || b < 0 || b >= MAX_USERS || a == b ||
        !n->profiles[a].active || !n->profiles[b].active || hasFriend(n, a, b)) return 0;
    if (!reserveNeighbor(&n->adjacent[a], n->adjacent[a].count + 1) ||
        !reserveNeighbor(&n->adjacent[b], n->adjacent[b].count + 1)) return -1;
    n->adjacent[a].v[n->adjacent[a].count++] = b;
    n->adjacent[b].v[n->adjacent[b].count++] = a;
    n->friendshipCount++;
    return 1;
}

static int removeNeighbor(Neighbors *list, int target) {
    int i;
    for (i = 0; i < list->count; i++) {
        if (list->v[i] == target) {
            if (i + 1 < list->count)
                memmove(&list->v[i], &list->v[i + 1],
                        (size_t)(list->count - i - 1) * sizeof(int));
            list->count--;
            return 1;
        }
    }
    return 0;
}

static int disconnectProfiles(Network *n, int a, int b) {
    if (a < 0 || b < 0 || a == b || !n->profiles[a].active ||
        !n->profiles[b].active || !hasFriend(n, a, b)) return 0;
    removeNeighbor(&n->adjacent[a], b);
    removeNeighbor(&n->adjacent[b], a);
    n->friendshipCount--;
    return 1;
}

static void deleteProfile(Network *n, int a) {
    while (n->adjacent[a].count) {
        int b = n->adjacent[a].v[n->adjacent[a].count - 1];
        disconnectProfiles(n, a, b);
    }
    free(n->adjacent[a].v);
    memset(&n->adjacent[a], 0, sizeof(n->adjacent[a]));
    mapDelete(n, n->profiles[a].handle);
    memset(&n->profiles[a], 0, sizeof(n->profiles[a]));
    n->userCount--;
}

static void queueInit(Queue *q) { memset(q, 0, sizeof(*q)); }
static void queuePush(Queue *q, int x) {
    q->data[q->rear] = x;
    q->rear = (q->rear + 1) % MAX_USERS;
    q->count++;
}
static int queuePop(Queue *q) {
    int result = q->data[q->front];
    q->front = (q->front + 1) % MAX_USERS;
    q->count--;
    return result;
}

/* Performs a complete BFS; predecessor -1 signals the origin/unreachable. */
static void bfs(const Network *n, int source, int distance[MAX_USERS],
                int predecessor[MAX_USERS]) {
    int i;
    Queue q;
    queueInit(&q);
    for (i = 0; i < MAX_USERS; i++) { distance[i] = -1; predecessor[i] = -1; }
    distance[source] = 0;
    queuePush(&q, source);
    while (q.count) {
        int u = queuePop(&q);
        for (i = 0; i < n->adjacent[u].count; i++) {
            int v = n->adjacent[u].v[i];
            if (distance[v] != -1) continue;
            distance[v] = distance[u] + 1;
            predecessor[v] = u;
            queuePush(&q, v);
        }
    }
}

static int bitCount(unsigned mask) {
    int count = 0;
    while (mask) { count += (int)(mask & 1u); mask >>= 1; }
    return count;
}

static void printInterests(unsigned mask) {
    int i, first = 1;
    for (i = 0; i < 8; i++) if (mask & (1u << i)) {
        printf("%s%s", first ? "" : ", ", interestNames[i]); first = 0;
    }
    if (first) printf("None specified");
}

static int compareIndexByHandle(const void *left, const void *right, void *context) {
    const Network *n = (const Network *)context;
    int a = *(const int *)left, b = *(const int *)right;
    return strcmp(n->profiles[a].handle, n->profiles[b].handle);
}

/* Portable insertion sort with an explicit context (no nonstandard qsort_r). */
static void sortIndices(const Network *n, int list[], int count) {
    int i, j, key;
    for (i = 1; i < count; i++) {
        key = list[i]; j = i - 1;
        while (j >= 0 && compareIndexByHandle(&list[j], &key, (void *)n) > 0) {
            list[j + 1] = list[j]; j--;
        }
        list[j + 1] = key;
    }
}

static void printProfile(const Network *n, int index) {
    const Profile *p = &n->profiles[index];
    int friends[MAX_USERS], i, count = n->adjacent[index].count;
    banner("PROFILE AND FRIENDS");
    printf("  @%-20s  ID #%u\n", p->handle, p->id);
    printf("  Name          : %s\n", p->name);
    printf("  City          : %s\n", p->city);
    printf("  Friends       : %d\n", count);
    printf("  Interests     : "); printInterests(p->interests); putchar('\n');
    printf("  Connections   : ");
    for (i = 0; i < count; i++) friends[i] = n->adjacent[index].v[i];
    sortIndices(n, friends, count);
    if (!count) puts("None yet");
    else {
        for (i = 0; i < count; i++)
            printf("%s@%s", i ? ", " : "", n->profiles[friends[i]].handle);
        putchar('\n');
    }
}

static int promptHandle(const Network *n, const char *message) {
    char h[HANDLE_LEN + 2];
    if (!inputLine(message, h, sizeof(h))) return -1;
    normalizeHandle(h);
    if (!validHandle(h) || mapGet(n, h) == -1) {
        printf("  [!] No matching profile for '@%s'.\n", h);
        return -1;
    }
    return mapGet(n, h);
}

static int promptPair(const Network *n, int *a, int *b) {
    *a = promptHandle(n, "  First @handle: ");
    if (*a < 0) return 0;
    *b = promptHandle(n, "  Second @handle: ");
    if (*b < 0) return 0;
    if (*a == *b) { puts("  [!] Select two different profiles."); return 0; }
    return 1;
}

static void listProfiles(const Network *n) {
    int indices[MAX_USERS], count = 0, i;
    banner("ALL USERS (ALPHABETICAL)");
    printf("  %-5s %-21s %-24s %-16s %7s\n", "ID", "HANDLE", "DISPLAY NAME", "CITY", "FRIENDS");
    divider();
    for (i = 0; i < MAX_USERS; i++) if (n->profiles[i].active) indices[count++] = i;
    sortIndices(n, indices, count);
    for (i = 0; i < count; i++) {
        int x = indices[i];
        printf("  %-5u @%-20s %-24.24s %-16.16s %7d\n",
               n->profiles[x].id, n->profiles[x].handle, n->profiles[x].name,
               n->profiles[x].city, n->adjacent[x].count);
    }
    if (!count) puts("  No profiles in this dataset.");
    printf("\n  %d active profiles.\n", count);
}

static int promptInterestMask(unsigned *mask) {
    int i, selection;
    *mask = 0;
    puts("  Optional interests (enter a number, or 0 to skip/finish):");
    for (i = 0; i < 8; i++) printf("    %d %-12s%s", i + 1, interestNames[i], i % 2 ? "\n" : "     ");
    for (;;) {
        selection = choose("  Choose 0-8: ", 0, 8);
        if (selection < 0) return 0;
        if (!selection) break;
        *mask ^= (1u << (selection - 1));
        printf("  Updated: "); printInterests(*mask); putchar('\n');
    }
    return 1;
}

/* The following declared after snapshot I/O implementation. */
static int autoSave(Network *n);

static void createProfileMenu(Network *n) {
    char handle[HANDLE_LEN + 2], name[NAME_LEN + 1], city[CITY_LEN + 1];
    unsigned interests;
    int slot;
    banner("CREATE A NEW PROFILE");
    if (n->userCount >= MAX_USERS) { puts("  [!] Profile limit reached (256)."); return; }
    if (n->nextId == UINT_MAX) { puts("  [!] Unique ID space exhausted."); return; }
    if (!inputLine("  Unique @handle (3-20 chars): ", handle, sizeof(handle))) return;
    normalizeHandle(handle);
    if (!validHandle(handle)) {
        puts("  [!] Use 3-20 characters: start with a letter, then a-z, 0-9, _. "); return;
    }
    if (mapGet(n, handle) >= 0) { puts("  [!] This handle is already registered."); return; }
    if (!promptText("  Display name: ", name, sizeof(name))) return;
    if (!promptText("  City: ", city, sizeof(city))) return;
    if (!promptInterestMask(&interests)) return;
    slot = registerProfile(n, n->nextId, handle, name, city, interests, 1);
    if (slot == -1) { puts("  [!] Unable to register profile."); return; }
    n->nextId++;
    printf("  [OK] @%s created with permanent ID #%u.\n", handle, n->profiles[slot].id);
    autoSave(n);
}

static void addConnectionMenu(Network *n) {
    int a, b, status;
    banner("ESTABLISH A FRIENDSHIP");
    if (!promptPair(n, &a, &b)) return;
    status = connectProfiles(n, a, b);
    if (status == 1) {
        printf("  [OK] @%s <--> @%s are now connected.\n",
               n->profiles[a].handle, n->profiles[b].handle);
        autoSave(n);
    } else if (status == 0) puts("  [!] Friendship already exists. No duplicate edge added.");
    else puts("  [!] Memory allocation failed. Friendship was not changed.");
}

static void removeConnectionMenu(Network *n) {
    int a, b, confirmation;
    banner("REMOVE A FRIENDSHIP");
    if (!promptPair(n, &a, &b)) return;
    if (!hasFriend(n, a, b)) { puts("  [!] These profiles are not directly connected."); return; }
    confirmation = choose("  Remove this undirected connection? (1 Yes / 0 No): ", 0, 1);
    if (confirmation != 1) return;
    disconnectProfiles(n, a, b);
    puts("  [OK] Both ends of the friendship were removed.");
    autoSave(n);
}

static void deleteProfileMenu(Network *n) {
    char proof[HANDLE_LEN + 2];
    int x;
    banner("DELETE A USER");
    x = promptHandle(n, "  Profile to delete @handle: ");
    if (x < 0) return;
    printf("  This removes @%s and its %d friendships.\n",
           n->profiles[x].handle, n->adjacent[x].count);
    if (!inputLine("  Type the exact @handle (without @) to confirm: ", proof, sizeof(proof))) return;
    if (strcmp(proof, n->profiles[x].handle) != 0) {
        puts("  Cancelled. Confirmation did not match."); return;
    }
    deleteProfile(n, x);
    puts("  [OK] Profile and all associated edges removed.");
    autoSave(n);
}

static void showMutualFriends(const Network *n, int a, int b) {
    int friends[MAX_USERS], count = 0, i;
    banner("MUTUAL FRIENDS");
    for (i = 0; i < n->adjacent[a].count; i++) {
        int v = n->adjacent[a].v[i];
        if (hasFriend(n, b, v)) friends[count++] = v;
    }
    sortIndices(n, friends, count);
    printf("  @%s and @%s share %d mutual friend%s.\n",
           n->profiles[a].handle, n->profiles[b].handle, count, count == 1 ? "" : "s");
    for (i = 0; i < count; i++)
        printf("    %2d. @%-20s %s\n", i + 1,
               n->profiles[friends[i]].handle, n->profiles[friends[i]].name);
    if (!count) puts("  No mutual connections found.");
}

static void mutualMenu(const Network *n) {
    int a, b;
    puts("\n  This feature finds people who are friends with BOTH users.");
    if (!promptPair(n, &a, &b)) return;
    showMutualFriends(n, a, b);
}

static void showShortestPath(const Network *n, int a, int b) {
    int distance[MAX_USERS], previous[MAX_USERS];
    int path[MAX_USERS], length = 0, current, i;
    banner("SHORTEST FRIENDSHIP CONNECTION (BFS)");
    bfs(n, a, distance, previous);
    if (distance[b] < 0) {
        printf("  [DISCONNECTED] No friendship chain links @%s to @%s.\n",
               n->profiles[a].handle, n->profiles[b].handle);
        puts("  These users belong to separate friendship groups.");
        return;
    }
    for (current = b; current != -1; current = previous[current])
        path[length++] = current;
    printf("  SHORTEST CHAIN  |  %d hop%s / %d profile%s\n\n  ",
           distance[b], distance[b] == 1 ? "" : "s",
           length, length == 1 ? "" : "s");
    for (i = length - 1; i >= 0; i--)
        printf("@%s%s", n->profiles[path[i]].handle,
               i ? "  -->  " : "\n");
    puts("\n  The path above uses the fewest friendship links.");
}

static void pathMenu(const Network *n) {
    int a, b;
    puts("\n  Find the fewest friendship steps connecting two people.");
    if (!promptPair(n, &a, &b)) return;
    showShortestPath(n, a, b);
}

static int compareRecommendations(const void *a, const void *b) {
    const Recommendation *x = (const Recommendation *)a;
    const Recommendation *y = (const Recommendation *)b;
    if (x->score != y->score) return (x->score < y->score) ? 1 : -1;
    if (x->mutual != y->mutual) return (x->mutual < y->mutual) ? 1 : -1;
    return (x->index < y->index) ? -1 : (x->index > y->index);
}

static void showRecommendations(const Network *n, int a) {
    int i, j, count = 0, k;
    Recommendation suggestions[MAX_USERS];
    int candidateMutual[MAX_USERS] = {0};
    banner("FRIEND RECOMMENDATIONS");
    for (i = 0; i < n->adjacent[a].count; i++) {
        int neighbor = n->adjacent[a].v[i];
        for (j = 0; j < n->adjacent[neighbor].count; j++) {
            int candidate = n->adjacent[neighbor].v[j];
            if (candidate != a && !hasFriend(n, a, candidate) &&
                n->profiles[candidate].discoverable)
                candidateMutual[candidate]++;
        }
    }
    for (i = 0; i < MAX_USERS; i++) if (candidateMutual[i] > 0) {
        Recommendation r;
        r.index = i;
        r.mutual = candidateMutual[i];
        r.shared = bitCount(n->profiles[a].interests & n->profiles[i].interests);
        r.sameCity = sameCity(n->profiles[a].city, n->profiles[i].city);
        /* One extra mutual connection outranks all possible profile bonuses. */
        r.score = r.mutual * 100 + r.shared * 10 + r.sameCity * 5;
        suggestions[count++] = r;
    }
    qsort(suggestions, (size_t)count, sizeof(suggestions[0]), compareRecommendations);
    puts("  Suggestions are based on mutual friends, interests and city.");
    puts("  People you are already friends with are not suggested.\n");
    if (!count) { puts("  No two-hop candidates found. Try adding more connections."); return; }
    printf("  %-4s %-20s %7s  %s\n", "NO.", "PERSON", "MUTUAL", "CITY");
    divider();
    for (i = 0; i < count && i < MAX_RESULTS; i++) {
        int displayed = 0;
        const Recommendation *r = &suggestions[i];
        printf("  %-4d @%-19s %7d  %s\n",
               i + 1, n->profiles[r->index].handle,
               r->mutual, n->profiles[r->index].city);
        printf("       Why: ");
        for (j = 0; j < n->adjacent[a].count && displayed < 3; j++) {
            int f = n->adjacent[a].v[j];
            if (hasFriend(n, r->index, f)) {
                printf("%svia @%s", displayed ? ", " : "", n->profiles[f].handle);
                displayed++;
            }
        }
        if (r->mutual > displayed) printf(" (+%d more)", r->mutual - displayed);
        if (r->shared) { printf(" | shared interests: "); printInterests(n->profiles[a].interests & n->profiles[r->index].interests); }
        if (r->sameCity) printf(" | same city");
        putchar('\n');
    }
    k = count - MAX_RESULTS;
    if (k > 0) printf("\n  Showing top %d of %d suggestions.\n", MAX_RESULTS, count);
}

static void recommendationsMenu(const Network *n) {
    int a;
    puts("\n  Find new friends through people you already know.");
    a = promptHandle(n, "  Recommendations for @handle: ");
    if (a >= 0) showRecommendations(n, a);
}

/* Snapshot: strict, versioned, readable text. Writes old snapshot to a backup
 * before replacing. A power loss between file renames can still require backup
 * recovery; this is not a database transaction or a security solution. */
static int saveNetwork(const Network *n) {
    const char *saveFile = demoMode ? DEMO_SAVE_FILE : SAVE_FILE;
    const char *backupFile = demoMode ? DEMO_BACKUP_FILE : BACKUP_FILE;
    const char *tempFile = demoMode ? DEMO_TEMP_FILE : TEMP_FILE;
    FILE *out = fopen(tempFile, "w");
    int i, j, ok = 1, hadOriginal = 0;
    if (!out) { perror("  [!] Cannot open temporary snapshot"); return 0; }
    if (fprintf(out, "LINKLENS|1|%u|%d|%d\n", n->nextId, n->userCount,
                n->friendshipCount) < 0) ok = 0;
    for (i = 0; i < MAX_USERS && ok; i++) if (n->profiles[i].active) {
        const Profile *p = &n->profiles[i];
        if (fprintf(out, "U|%u|%s|%s|%s|%u|%d\n",
                    p->id, p->handle, p->name, p->city, p->interests,
                    p->discoverable) < 0) ok = 0;
    }
    for (i = 0; i < MAX_USERS && ok; i++) if (n->profiles[i].active) {
        for (j = 0; j < n->adjacent[i].count; j++) {
            int b = n->adjacent[i].v[j];
            if (i < b && fprintf(out, "F|%u|%u\n",
                                 n->profiles[i].id, n->profiles[b].id) < 0) ok = 0;
        }
    }
    if (fflush(out) != 0) ok = 0;
    if (fclose(out) != 0) ok = 0;
    if (!ok) { remove(tempFile); puts("  [!] Snapshot write failed."); return 0; }
    { FILE *old = fopen(saveFile, "rb"); if (old) { hadOriginal = 1; fclose(old); } }
    if (hadOriginal) {
        /* If backup deletion fails, do not put the existing data at risk. */
        { FILE *back = fopen(backupFile, "rb");
          if (back) { fclose(back); if (remove(backupFile) != 0) {
              remove(tempFile); puts("  [!] Cannot replace backup; original preserved."); return 0;
          } }
        }
        if (rename(saveFile, backupFile) != 0) {
            remove(tempFile);
            puts("  [!] Cannot prepare backup; original snapshot preserved."); return 0;
        }
    }
    if (rename(tempFile, saveFile) != 0) {
        if (hadOriginal && rename(backupFile, saveFile) != 0)
            puts("  [!] Original saved in .bak; manual recovery may be required.");
        remove(tempFile);
        puts("  [!] Snapshot replacement failed.");
        return 0;
    }
    return 1;
}

static int autoSave(Network *n) {
    n->dirty = 1;
    if (!saveNetwork(n)) {
        puts("  [WARNING] Changes have not been saved. Check folder permissions.");
        return 0;
    }
    n->dirty = 0;
    puts("  [OK] Changes saved.");
    return 1;
}

/* Splits on every delimiter, including empty fields. */
static int splitFields(char *line, char *fields[], int wanted) {
    int count = 0;
    char *p = line;
    while (count < wanted) {
        char *sep;
        fields[count++] = p;
        sep = strchr(p, '|');
        if (!sep) return count;
        *sep = '\0'; p = sep + 1;
    }
    return wanted + 1; /* final field contained an extra separator */
}

static int readRecord(FILE *f, char *buffer, size_t capacity) {
    size_t len;
    if (!fgets(buffer, (int)capacity, f)) return 0;
    len = strlen(buffer);
    if (len && buffer[len - 1] == '\n') buffer[--len] = '\0';
    else if (!feof(f)) return -1;
    if (len && buffer[len - 1] == '\r') buffer[--len] = '\0';
    return 1;
}

static int loadNetworkFrom(const char *path, Network *destination) {
    Network *temp;
    FILE *f;
    char buffer[LINE_LEN], *parts[7];
    unsigned version, nextId, users, edges, value, maxId = 0;
    unsigned i, a, b, mask, visible;
    int status, ok = 0;
    f = fopen(path, "rb");
    if (!f) return 0;
    temp = (Network *)calloc(1, sizeof(Network));
    if (!temp) { fclose(f); return 0; }
    initNetwork(temp);
    status = readRecord(f, buffer, sizeof(buffer));
    if (status != 1 || splitFields(buffer, parts, 5) != 5 ||
        strcmp(parts[0], "LINKLENS") ||
        !parseUnsigned(parts[1], &version) || version != 1 ||
        !parseUnsigned(parts[2], &nextId) ||
        !parseUnsigned(parts[3], &users) ||
        !parseUnsigned(parts[4], &edges) ||
        users > MAX_USERS || edges > users * (users - 1) / 2 || !nextId) goto done;
    for (i = 0; i < users; i++) {
        status = readRecord(f, buffer, sizeof(buffer));
        if (status != 1 || splitFields(buffer, parts, 7) != 7 ||
            strcmp(parts[0], "U") || !parseUnsigned(parts[1], &value) ||
            !parseUnsigned(parts[5], &mask) ||
            !parseUnsigned(parts[6], &visible) || visible > 1u) goto done;
        if (registerProfile(temp, value, parts[2], parts[3], parts[4],
                            mask, (int)visible) < 0) goto done;
        if (value > maxId) maxId = value;
    }
    if (nextId <= maxId) goto done;
    for (i = 0; i < edges; i++) {
        int x, y;
        status = readRecord(f, buffer, sizeof(buffer));
        if (status != 1 || splitFields(buffer, parts, 3) != 3 ||
            strcmp(parts[0], "F") ||
            !parseUnsigned(parts[1], &a) || !parseUnsigned(parts[2], &b)) goto done;
        x = findId(temp, a); y = findId(temp, b);
        if (connectProfiles(temp, x, y) != 1) goto done;
    }
    if (readRecord(f, buffer, sizeof(buffer)) != 0 || ferror(f)) goto done;
    if (temp->userCount != (int)users || temp->friendshipCount != (int)edges) goto done;
    temp->nextId = nextId;
    clearNetwork(destination);
    *destination = *temp; /* ownership of adjacency buffers transfers */
    ok = 1;
 done:
    if (!ok) clearNetwork(temp);
    free(temp);
    fclose(f);
    return ok;
}

static int addDemoUser(Network *n, const char *handle, const char *name,
                       const char *city, unsigned interests, int discoverable) {
    int slot = registerProfile(n, n->nextId, handle, name, city, interests, discoverable);
    if (slot >= 0) n->nextId++;
    return slot;
}

static int demoEdge(Network *n, const char *a, const char *b) {
    return connectProfiles(n, mapGet(n, a), mapGet(n, b)) == 1;
}

static int seedDemo(Network *n) {
    /* Fictional users and sample friendships for demonstration. */
    static const struct {
        const char *handle, *name, *city;
        unsigned interests;
        int visible;
    } people[] = {
        {"aarav", "Aarav Mehta", "Mumbai", 1u|2u|32u, 1},
        {"diya", "Diya Shah", "Mumbai", 1u|4u|128u, 1},
        {"kabir", "Kabir Rao", "Pune", 1u|2u|64u, 1},
        {"meera", "Meera Iyer", "Mumbai", 4u|16u|32u, 1},
        {"zoya", "Zoya Khan", "Pune", 1u|4u|64u, 1},
        {"ishaan", "Ishaan Nair", "Bengaluru", 1u|8u|64u, 1},
        {"rhea", "Rhea Kapoor", "Mumbai", 8u|16u|128u, 1},
        {"neil", "Neil Patel", "Pune", 2u|8u|32u, 1},
        {"tara", "Tara Sen", "Delhi", 2u|4u|128u, 1},
        {"vihaan", "Vihaan Das", "Delhi", 1u|2u|16u, 1},
        {"anaya", "Anaya Bose", "Delhi", 4u|32u|128u, 1},
        {"reyansh", "Reyansh Gill", "Delhi", 2u|8u|64u, 1},
        {"sana", "Sana Ali", "Hyderabad", 1u|32u|128u, 0},
        {"omkar", "Omkar Joshi", "Hyderabad", 1u|16u|64u, 1},
        {"priya", "Priya Menon", "Hyderabad", 4u|8u|32u, 1},
        {"arjun", "Arjun Verma", "Chennai", 1u|2u|64u, 1}
    };
    static const char *pairs[][2] = {
        {"aarav","diya"},{"aarav","kabir"},{"diya","kabir"},
        {"diya","meera"},{"kabir","zoya"},{"zoya","ishaan"},
        {"meera","rhea"},{"rhea","neil"},{"neil","ishaan"},
        {"kabir","neil"},
        {"tara","vihaan"},{"vihaan","anaya"},{"anaya","reyansh"},
        {"reyansh","tara"},
        {"sana","omkar"},{"omkar","priya"},{"priya","sana"}
    };
    size_t i;
    clearNetwork(n);
    for (i = 0; i < sizeof(people)/sizeof(people[0]); i++)
        if (addDemoUser(n, people[i].handle, people[i].name, people[i].city,
                        people[i].interests, people[i].visible) < 0) return 0;
    for (i = 0; i < sizeof(pairs)/sizeof(pairs[0]); i++)
        if (!demoEdge(n, pairs[i][0], pairs[i][1])) return 0;
    n->dirty = 1;
    return 1;
}

static int confirmReplacement(const char *mode) {
    char answer[16];
    printf("\n  %s will replace your previously saved personal network.\n", mode);
    if (!inputLine("  Type YES to confirm, anything else to cancel: ", answer, sizeof(answer)))
        return 0;
    if (strcmp(answer, "YES") != 0) {
        puts("  Cancelled. Saved data have not been changed.");
        return 0;
    }
    return 1;
}

/* Build sample data separately first, so an allocation failure cannot erase
   the user's current in-memory network. */
static int replaceWithDemo(Network *n) {
    Network *example = (Network *)calloc(1, sizeof(Network));
    if (!example) return 0;
    initNetwork(example);
    if (!seedDemo(example)) {
        clearNetwork(example);
        free(example);
        return 0;
    }
    clearNetwork(n);
    *n = *example;
    free(example);               /* Lists now belong to n. */
    n->dirty = 1;
    return 1;
}

/* Start with sample data or a new empty network. Saved work is optional.
   Whichever choice is made, the user goes to the SAME full main menu. */
static int startingMenu(Network *n, int savedAvailable) {
    int option;
    for (;;) {
        banner("WELCOME TO LINKLENS");
        puts("  Social Network Connection Analyzer");
        puts("  Explore mutual friends, shortest paths and friend suggestions.");
        puts("\n  HOW WOULD YOU LIKE TO START?");
        puts("  1. Use 16 fictional users and their friendships");
        puts("  2. Start empty and create my own users");
        if (savedAvailable)
            printf("  3. Continue saved work (%d users, %d friendships)\n",
                   n->userCount, n->friendshipCount);
        else
            puts("  3. Continue saved work (no save found)");
        puts("  0. Exit");
        divider();
        option = choose("  Choose 0-3: ", 0, 3);
        if (option <= 0) return 0;
        if (option == 3) {
            if (!savedAvailable) {
                puts("  No saved data found. Please choose 1 or 2.");
                continue;
            }
            puts("  [OK] Your previous network is ready.");
            return 1;
        }
        /* Loading fictional users never overwrites saved personal profiles. */
        if (savedAvailable && option == 2 &&
            !confirmReplacement("Starting an empty network"))
            continue;
        if (option == 1) {
            if (n->dirty && !autoSave(n)) {
                puts("  [!] Cannot protect unsaved changes. Example not loaded.");
                continue;
            }
            if (!replaceWithDemo(n)) {
                puts("  [ERROR] Could not load fictional users. Saved work is unchanged.");
                continue;
            }
            demoMode = 1;
            puts("\n  [OK] Example network ready: 16 users, 17 friendships.");
            puts("  Try menu options 1, 3, 4 and 5 to explore it.");
        } else {
            demoMode = 0;
            clearNetwork(n);
            n->dirty = 1;
            puts("\n  [OK] Your network is empty. Choose option 2 to add users.");
        }
        if (!autoSave(n))
            puts("  [!] The network is in memory, but the disk save failed.");
        return 1;
    }
}

static void viewUsersMenu(const Network *n) {
    int selection, user;
    listProfiles(n);
    if (n->userCount == 0) return;
    selection = choose("  View a user's friends? (1 Yes / 0 No): ", 0, 1);
    if (selection != 1) return;
    user = promptHandle(n, "  Enter username: ");
    if (user >= 0) printProfile(n, user);
}

static void manageMenu(Network *n) {
    int selection;
    for (;;) {
        banner("MANAGE USERS AND FRIENDSHIPS");
        puts("  1. Add a new user");
        puts("  2. Add a friendship");
        puts("  3. Remove a friendship");
        puts("  4. Delete a user");
        puts("  0. Back to main menu");
        selection = choose("  Your choice: ", 0, 4);
        if (selection <= 0) return;
        switch (selection) {
            case 1: createProfileMenu(n); break;
            case 2: addConnectionMenu(n); break;
            case 3: removeConnectionMenu(n); break;
            case 4: deleteProfileMenu(n); break;
        }
        waitForEnter();
    }
}

/* Menu option 6 is for switching to the demo LATER if you started empty.
   It is not a second startup screen. */
static void exampleNetworkMenu(Network *n) {
    banner("EXPLORE FICTIONAL NETWORK");
    puts("  This example contains 16 users and 17 friendships.");
    puts("  You can then run the mutual friend, BFS and suggestion features.");
    /* Preserve the personal save and open a separate demonstration workspace. */
    if (n->dirty && !autoSave(n)) {
        puts("  [!] Existing changes could not be saved. Example not loaded.");
        return;
    }
    if (!replaceWithDemo(n)) {
        puts("  [ERROR] Could not load example network. Current work is unchanged.");
        return;
    }
    demoMode = 1;
    autoSave(n);
    puts("  [OK] Demo network loaded!");
    puts("  For mutual friends, enter: aarav and kabir");
    puts("  For shortest path, enter: aarav and ishaan");
    puts("  For friend recommendations, enter: aarav");
}

static void dashboard(const Network *n) {
    banner("LINKLENS - SOCIAL NETWORK CONNECTION ANALYZER");
    printf("  Users: %d  |  Friendships: %d\n",
           n->userCount, n->friendshipCount);
    puts("\n  MAIN MENU");
    puts("  1. View users and their friends");
    puts("  2. Manage users and friendships");
    puts("  3. Find mutual friends");
    puts("  4. Find shortest connection (BFS)");
    puts("  5. Get friend recommendations");
    puts("  6. Explore ready-made fictional network");
    puts("  0. Exit");
    divider();
    if (n->userCount == 0)
        puts("  TIP: Start with 2 to add users, or 6 to load the example network.");
    puts("  Enter the number of an option and press Enter.");
}

int main(void) {
    Network *n;
    int choice, savedAvailable = 0;
    n = (Network *)calloc(1, sizeof(Network));
    if (!n) {
        fputs("Not enough memory.\n", stderr);
        return EXIT_FAILURE;
    }
    initNetwork(n);

    if (loadNetworkFrom(SAVE_FILE, n)) {
        savedAvailable = 1;
    } else if (loadNetworkFrom(BACKUP_FILE, n)) {
        savedAvailable = 1;
        n->dirty = 1;
        puts("  [INFO] Recovered an earlier save from the backup file.");
    }

    if (!startingMenu(n, savedAvailable)) {
        clearNetwork(n);
        free(n);
        puts("Goodbye!");
        return 0;
    }

    for (;;) {
        dashboard(n);
        choice = choose("  Enter your choice: ", 0, 6);
        if (choice <= 0) break;
        switch (choice) {
            case 1: viewUsersMenu(n); break;
            case 2: manageMenu(n); break;
            case 3: mutualMenu(n); break;
            case 4: pathMenu(n); break;
            case 5: recommendationsMenu(n); break;
            case 6: exampleNetworkMenu(n); break;
        }
        if (choice != 2) waitForEnter();
    }
    if (n->dirty) {
        puts("  Saving unsaved changes before exit...");
        if (!autoSave(n))
            puts("  [WARNING] Unable to save the latest changes.");
    }
    clearNetwork(n);
    free(n);
    puts("\n  Thank you for using LinkLens!\n");
    return 0;
}
