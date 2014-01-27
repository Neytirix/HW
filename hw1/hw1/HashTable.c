/*
 * Copyright 2011 Steven Gribble
 *
 *  This file is part of the UW CSE 333 course project sequence
 *  (333proj).
 *
 *  333proj is free software: you can redistribute it and/or modify
 *  it under the terms of the GNU General Public License as published by
 *  the Free Software Foundation, either version 3 of the License, or
 *  (at your option) any later version.
 *
 *  333proj is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License
 *  along with 333proj.  If not, see <http://www.gnu.org/licenses/>.
 */

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

#include "CSE333.h"
#include "HashTable.h"
#include "HashTable_priv.h"

// A private utility function to grow the hashtable (increase
// the number of buckets) if its load factor has become too high.
static void ResizeHashtable(HashTable ht);

// A private function to Search in the list,
//          find if there already exist the given key.
static int SearchKey(LinkedList list, HTKey_t key,
                        HTKeyValue *oldkeyvalue, int operation);

// a free function that does nothing
static void LLNullFree(LLPayload_t freeme) { }
static void HTNullFree(HTValue_t freeme) { }

HashTable AllocateHashTable(HWSize_t num_buckets) {
  HashTable ht;
  HWSize_t  i;

  // defensive programming
  if (num_buckets == 0) {
    return NULL;
  }

  // allocate the hash table record
  ht = (HashTable) malloc(sizeof(HashTableRecord));
  if (ht == NULL) {
    return NULL;
  }

  // initialize the record
  ht->num_buckets = num_buckets;
  ht->num_elements = 0;
  ht->buckets =
    (LinkedList *) malloc(num_buckets * sizeof(LinkedList));
  if (ht->buckets == NULL) {
    // make sure we don't leak!
    free(ht);
    return NULL;
  }
  for (i = 0; i < num_buckets; i++) {
    ht->buckets[i] = AllocateLinkedList();
    if (ht->buckets[i] == NULL) {
      // allocating one of our bucket chain lists failed,
      // so we need to free everything we allocated so far
      // before returning NULL to indicate failure.  Since
      // we know the chains are empty, we'll pass in a
      // free function pointer that does nothing; it should
      // never be called.
      HWSize_t j;
      for (j = 0; j < i; j++) {
        FreeLinkedList(ht->buckets[j], LLNullFree);
      }
      free(ht);
      return NULL;
    }
  }

  return (HashTable) ht;
}

void FreeHashTable(HashTable table,
                   ValueFreeFnPtr value_free_function) {
  HWSize_t i;

  Verify333(table != NULL);  // be defensive

  // loop through and free the chains on each bucket
  for (i = 0; i < table->num_buckets; i++) {
    LinkedList  bl = table->buckets[i];
    HTKeyValue *nextKV;

    // pop elements off the the chain list, then free the list
    while (NumElementsInLinkedList(bl) > 0) {
      Verify333(PopLinkedList(bl, (LLPayload_t*)&nextKV));
      value_free_function(nextKV->value);
      free(nextKV);
    }
    // the chain list is empty, so we can pass in the
    // null free function to FreeLinkedList.
    FreeLinkedList(bl, LLNullFree);
  }

  // free the bucket array within the table record,
  // then free the table record itself.
  free(table->buckets);
  free(table);
}

HWSize_t NumElementsInHashTable(HashTable table) {
  Verify333(table != NULL);
  return table->num_elements;
}

HTKey_t FNVHash64(unsigned char *buffer, HWSize_t len) {
  // This code is adapted from code by Landon Curt Noll
  // and Bonelli Nicola:
  //
  // http://code.google.com/p/nicola-bonelli-repo/
  static const uint64_t FNV1_64_INIT = 0xcbf29ce484222325ULL;
  static const uint64_t FNV_64_PRIME = 0x100000001b3ULL;
  unsigned char *bp = (unsigned char *) buffer;
  unsigned char *be = bp + len;
  uint64_t hval = FNV1_64_INIT;

  /*
   * FNV-1a hash each octet of the buffer
   */
  while (bp < be) {
    /* xor the bottom with the current octet */
    hval ^= (uint64_t) * bp++;
    /* multiply by the 64 bit FNV magic prime mod 2^64 */
    hval *= FNV_64_PRIME;
  }
  /* return our new hash value */
  return hval;
}

HTKey_t FNVHashInt64(HTValue_t hashval) {
  unsigned char buf[8];
  int i;
  uint64_t hashme = (uint64_t)hashval;

  for (i = 0; i < 8; i++) {
    buf[i] = (unsigned char) (hashme & 0x00000000000000FFULL);
    hashme >>= 8;
  }
  return FNVHash64(buf, 8);
}

HWSize_t HashKeyToBucketNum(HashTable ht, HTKey_t key) {
  return key % ht->num_buckets;
}

// Search in the list, find if there already exist the given key.
//
// Arguments:
//
// - list: The list we will search the key in.
//
// - key: The key that we will search in the list.
//
// - oldkeyvalue: If such a key is already exist in the list,
//                 then the old key/value is returned via this return
//                  parameter to the caller.
//
// - operation: Delete the found exist old key/value and
//                   free the payload (value) if operation == 1.
//              Remains the same if operation == 0.
//
// Returns:
//
// - 0 on failure (e.g., out of memory).
//
// - +1 if a key is NOT found exist in the list.
//
// - +2 if a key is found exist in the list.
static int SearchKey(LinkedList list, HTKey_t key,
                        HTKeyValue *oldkeyvalue, int operation) {
  if (NumElementsInLinkedList(list) == 0) {
    // The given list is empty.
    return 1;
  }

  LLIter iter = LLMakeIterator(list, 0);
  if (iter == NULL) {
    // Fail to make an iterator (e.g., out of memory).
    return 0;
  }
  int status = 1;
  HTKeyValue *current = NULL;
  do {
    LLIteratorGetPayload(iter, (void **) &current);
    if (current->key == key) {
      // Found such key is exist in the list.
      *oldkeyvalue = *current;
      if (operation == 1) {
        // Delete the Node and free the payload.
        LLIteratorDelete(iter, &LLNullFree);
        free(current);
      }
      status = 2;
      break;
    }
  } while (LLIteratorNext(iter));
  LLIteratorFree(iter);
  // Not found, return 1.
  return status;
}




int InsertHashTable(HashTable table,
                    HTKeyValue newkeyvalue,
                    HTKeyValue *oldkeyvalue) {
  HWSize_t insertbucket;
  LinkedList insertchain;

  Verify333(table != NULL);
  ResizeHashtable(table);

  // calculate which bucket we're inserting into,
  // grab its linked list chain
  insertbucket = HashKeyToBucketNum(table, newkeyvalue.key);
  insertchain = table->buckets[insertbucket];

  // Step 1 -- finish the implementation of InsertHashTable.
  // This is a fairly complex task, so you might decide you want
  // to define/implement a helper function that helps you find
  // and optionally remove a key within a chain, rather than putting
  // all that logic inside here.  You might also find that your helper
  // can be reused in steps 2 and 3.
  HTKeyValue *newnode = (HTKeyValue *) malloc(sizeof(HTKeyValue));
  if (newnode == NULL) {
    // Error, out of memory.
    return 0;
  }
  *newnode = newkeyvalue;

  int searchresult = SearchKey(insertchain, newnode->key, oldkeyvalue, 1);

  if (searchresult != 0 && PushLinkedList(insertchain, newnode)) {
    // Successfully inserted.
    if (searchresult == 1) {
      // The key is not in the list yet.
      table->num_elements++;
    }
    // If the key has a duplication in the list, nothing to do,
    //   since return value is searchresult = 2
    //          and "oldkeyvalue" is updated by SearchKey.
    return searchresult;
  }

  // Insertion failed.
  free(newnode);
  return 0;
}

int LookupHashTable(HashTable table,
                    HTKey_t key,
                    HTKeyValue *keyvalue) {
  Verify333(table != NULL);

  // Step 2 -- implement LookupHashTable.

  // calculate which bucket we're searching in,
  // grab its linked list chain
  HWSize_t searchbucket = HashKeyToBucketNum(table, key);
  LinkedList searchchain = table->buckets[searchbucket];

  return SearchKey(searchchain, key, keyvalue, 0) - 1;
}

int RemoveFromHashTable(HashTable table,
                        HTKey_t key,
                        HTKeyValue *keyvalue) {
  Verify333(table != NULL);

  // Step 3 -- implement RemoveFromHashTable.

  // calculate which bucket we're searching in,
  // grab its linked list chain
  HWSize_t searchbucket = HashKeyToBucketNum(table, key);
  LinkedList searchchain = table->buckets[searchbucket];

  int searchresult = SearchKey(searchchain, key, keyvalue, 1);

  if (searchresult == 2) {
    // Key found.
    table->num_elements--;
  }

  // Key Not found, or error occurs (e.g., out of memory).
  return searchresult - 1;
}

HTIter HashTableMakeIterator(HashTable table) {
  HTIterRecord *iter;
  HWSize_t      i;

  Verify333(table != NULL);  // be defensive

  // malloc the iterator
  iter = (HTIterRecord *) malloc(sizeof(HTIterRecord));
  if (iter == NULL) {
    return NULL;
  }

  // if the hash table is empty, the iterator is immediately invalid,
  // since it can't point to anything.
  if (table->num_elements == 0) {
    iter->is_valid = false;
    iter->ht = table;
    iter->bucket_it = NULL;
    return iter;
  }

  // initialize the iterator.  there is at least one element in the
  // table, so find the first element and point the iterator at it.
  iter->is_valid = true;
  iter->ht = table;
  for (i = 0; i < table->num_buckets; i++) {
    if (NumElementsInLinkedList(table->buckets[i]) > 0) {
      iter->bucket_num = i;
      break;
    }
  }
  Verify333(i < table->num_buckets);  // make sure we found it.
  iter->bucket_it = LLMakeIterator(table->buckets[iter->bucket_num], 0UL);
  if (iter->bucket_it == NULL) {
    // out of memory!
    free(iter);
    return NULL;
  }
  return iter;
}

void HTIteratorFree(HTIter iter) {
  Verify333(iter != NULL);
  if (iter->bucket_it != NULL) {
    LLIteratorFree(iter->bucket_it);
    iter->bucket_it = NULL;
  }
  iter->is_valid = false;
  free(iter);
}

int HTIteratorNext(HTIter iter) {
  Verify333(iter != NULL);

  // Step 4 -- implement HTIteratorNext.
  if (iter->bucket_it != NULL && LLIteratorNext(iter->bucket_it)) {
    // Best case that we can just move on the iterator.
    return 1;
  }

  // Search the next bucket to iterate.
  int currentbucket = iter->bucket_num + 1;
  while (currentbucket < iter->ht->num_buckets &&
          NumElementsInLinkedList(iter->ht->buckets[currentbucket]) == 0) {
    currentbucket++;
  }

  if (currentbucket < iter->ht->num_buckets) {
    // A valid bucket is found, free old iterator and make a new one.
    LLIteratorFree(iter->bucket_it);
    iter->bucket_num = currentbucket;
    iter->bucket_it = LLMakeIterator(iter->ht->buckets[iter->bucket_num], 0);

    if (iter->bucket_it == NULL) {
      // Error occurs (e.g., out of memory).
      return 0;
    }
    return 1;
  }

  // The iterator (after moving it forward) is past the
  //   end of the table.
  iter->is_valid = false;

  return 0;
}

int HTIteratorPastEnd(HTIter iter) {
  Verify333(iter != NULL);

  // Step 5 -- implement HTIteratorPastEnd.
  return (!iter->is_valid) || (iter->ht == NULL) ||
                           (iter->ht->num_elements == 0);
}

int HTIteratorGet(HTIter iter, HTKeyValue *keyvalue) {
  Verify333(iter != NULL);

  // Step 6 -- implement HTIteratorGet.
  if (HTIteratorPastEnd(iter)) {
    // The iterator is past the end or it is invalid.
    return 0;
  }

  LLIteratorGetPayload(iter->bucket_it, (void **) &keyvalue);

  return 1;
}

int HTIteratorDelete(HTIter iter, HTKeyValue *keyvalue) {
  HTKeyValue kv;
  int res, retval;

  Verify333(iter != NULL);

  // Try to get what the iterator is pointing to.
  res = HTIteratorGet(iter, &kv);
  if (res == 0)
    return 0;

  // Advance the iterator.
  res = HTIteratorNext(iter);
  if (res == 0) {
    retval = 2;
  } else {
    retval = 1;
  }
  res = RemoveFromHashTable(iter->ht, kv.key, keyvalue);
  Verify333(res == 1);
  Verify333(kv.key == keyvalue->key);
  Verify333(kv.value == keyvalue->value);

  return retval;
}

static void ResizeHashtable(HashTable ht) {
  // Resize if the load factor is > 3.
  if (ht->num_elements < 3 * ht->num_buckets)
    return;

  // This is the resize case.  Allocate a new hashtable,
  // iterate over the old hashtable, do the surgery on
  // the old hashtable record and free up the new hashtable
  // record.
  HashTable newht = AllocateHashTable(ht->num_buckets * 9);

  // Give up if out of memory.
  if (newht == NULL)
    return;

  // Loop through the old ht with an iterator,
  // inserting into the new HT.
  HTIter it = HashTableMakeIterator(ht);
  if (it == NULL) {
    // Give up if out of memory.
    FreeHashTable(newht, &HTNullFree);
    return;
  }

  while (!HTIteratorPastEnd(it)) {
    HTKeyValue item, dummy;

    Verify333(HTIteratorGet(it, &item) == 1);
    if (InsertHashTable(newht, item, &dummy) != 1) {
      // failure, free up everything, return.
      HTIteratorFree(it);
      FreeHashTable(newht, &HTNullFree);
      return;
    }
    HTIteratorNext(it);
  }

  // Worked!  Free the iterator.
  HTIteratorFree(it);

  // Sneaky: swap the structures, then free the new table,
  // and we're done.
  {
    HashTableRecord tmp;

    tmp = *ht;
    *ht = *newht;
    *newht = tmp;
    FreeHashTable(newht, &HTNullFree);
  }

  return;
}
