// Browser-compatible crypto stub
// Uses Web Crypto API for hashing

export function createHash(algorithm: string) {
  let data = '';
  return {
    update(str: string) {
      data += str;
      return this;
    },
    digest(encoding: string) {
      // Simple browser-compatible hash using djb2 algorithm
      let hash = 5381;
      for (let i = 0; i < data.length; i++) {
        hash = ((hash << 5) + hash) + data.charCodeAt(i);
        hash = hash & hash; // Convert to 32bit integer
      }
      return Math.abs(hash).toString(16);
    }
  };
}

export default { createHash };
