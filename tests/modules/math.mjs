export const base = 20;

export function twice(value) {
  return value * 2;
}

export function unusedDynamicFeature() {
  return import("./never-loaded.mjs");
}
