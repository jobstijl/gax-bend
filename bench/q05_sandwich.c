// Q5 reference: gax unit_motor_sandwich_point (33 multiplies), the same
// tree of 2^D leaves x 2^L points as bench/q05_sandwich.bend, same sum order.
// clang -O3 -ffp-contract=off q05_sandwich.c -lpthread
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <pthread.h>
#include <time.h>
typedef struct { float c0x, c0y, c0z, c0w, c1x, c1y, c1z, c1w; } Motor;
typedef struct { float x, y, z, w; } Point;
static inline Point sandwich(Motor v, Point p) {
  float c0x = v.c0x, c0y = v.c0y, c0z = v.c0z, c0w = v.c0w, c1x = v.c1x, c1y = v.c1y, c1z = v.c1z, c1w = v.c1w;
  float px = p.x, py = p.y, pz = p.z, pw = p.w;
  float t2 = c1z * pw;
  float t3 = c0y * py + t2;
  float t4 = -c0z * px + t3;
  float t5 = c0y * pz;
  float t8 = -c0w * px + t5;
  float t9 = -c1y * pw + t8;
  float t12 = c1x * pw;
  float t13 = c0z * pz + t12;
  float t14 = -c0w * py + t13;
  float t15 = c1w * pw;
  float t17 = c0y * t15;
  float t19 = c0w * t9;
  float t22 = c0z * t15;
  float t23 = c0w * t14;
  float t25 = c0y * t9;
  float t27 = c0w * t15;
  float t28 = c0z * t4 + t19;
  float t29 = c0x * t14 + t17;
  float t30 = t28 - t29;
  float t33 = c0y * c0y;
  float t35 = c0w * c0w;
  float t36 = c0x * c0x + t33;
  float t37 = c0z * c0z + t35;
  float t38 = t36 + t37;
  float t39 = px * t38;
  float t40 = t30 * 2.0f + t39;
  float t41 = c0x * t9 + t23;
  float t42 = c0y * t4 + t22;
  float t43 = t41 - t42;
  float t45 = py * t38;
  float t46 = t43 * 2.0f + t45;
  float t47 = c0x * t4 + t25;
  float t48 = c0z * t14 + t27;
  float t49 = t47 + t48;
  float t51 = pz * t38;
  float t52 = -t49 * 2.0f + t51;
  float t53 = pw * t38;
  return (Point){ t40, t46, t52, t53 };
}
static inline Point gen(uint32_t i) {
  return (Point){ (float)(i & 1023u), (float)((i >> 10) & 1023u), (float)(i >> 20), 1.0f };
}
#define LEAF_LOG 12
static float leaf(uint32_t n, uint32_t i, float acc, Motor m) {
  for (; n; n--, i++) { Point q = sandwich(m, gen(i)); acc = acc + (((q.x + q.y) + q.z) + q.w); }
  return acc;
}
static float tree(uint32_t d, uint32_t i, Motor m) {
  if (d == 0) return leaf(1u << LEAF_LOG, i << LEAF_LOG, 0.0f, m);
  float a = tree(d - 1, i * 2, m), b = tree(d - 1, i * 2 + 1, m);
  return a + b;
}
typedef struct { uint32_t d, i; Motor m; float out; } Job;
static void *run(void *p) { Job *j = p; j->out = tree(j->d, j->i, j->m); return 0; }
// the top T levels are forked over 2^T threads, then summed in tree order
static float par(uint32_t d, uint32_t t, Motor m) {
  uint32_t n = 1u << t; Job *js = calloc(n, sizeof(Job)); pthread_t *th = calloc(n, sizeof(pthread_t));
  for (uint32_t k = 0; k < n; k++) { js[k] = (Job){ d - t, k, m, 0 }; pthread_create(&th[k], 0, run, &js[k]); }
  for (uint32_t k = 0; k < n; k++) pthread_join(th[k], 0);
  for (uint32_t w = n; w > 1; w /= 2) for (uint32_t k = 0; k < w / 2; k++) js[k].out = js[2 * k].out + js[2 * k + 1].out;
  float r = js[0].out; free(js); free(th); return r;
}
int main(int argc, char **argv) {
  uint32_t d = argc > 1 ? atoi(argv[1]) : 14, t = argc > 2 ? atoi(argv[2]) : 0;
  float k = (float)(time(0) & 1);   // 0 or 1, unknown to the compiler
  Motor m = { 0.8f, 0.36f, 0.48f, k * 0.0f, 0.1f, 0.2f, 0.3f, 0.05f };
  struct timespec a, b; clock_gettime(CLOCK_MONOTONIC, &a);
  float s = t ? par(d, t, m) : tree(d, 0, m);
  clock_gettime(CLOCK_MONOTONIC, &b);
  uint32_t bits; __builtin_memcpy(&bits, &s, 4);
  printf("sum %.9g bits %08x  %.3f s\n", s, bits, (b.tv_sec - a.tv_sec) + (b.tv_nsec - a.tv_nsec) * 1e-9);
}
