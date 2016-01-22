/*******************************************************************************
 * (C) 2016 Stanislav Moiseev. All rights reserved.
 ******************************************************************************/

#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#include <stdint.h>

#include "utils.h"
#include "binary.h"

void pred_read(FILE *fd, pred *pred) {
  uint64_t k = read_uint64(fd);
  assert(k == K);
  
  pred->arity = read_uint64(fd);
  pred->data = read_uint64(fd);
}

int class_read(FILE *fd, class *class) {
  /* the size of the basis */
  uint64_t size = read_uint64(fd);

  for(int64_t i = size; i > 0; --i) {
    pred pred;
    pred_read(fd, &pred);
    clone_insert_pred(&class->basis, &pred);
  }
  
  class->clone.data0 = read_uint32(fd);
  class->clone.data1 = read_uint32(fd);
  assert(CLONE_DATA2_SIZE == 8);
  for(int64_t offset = 0; offset < CLONE_DATA2_SIZE; ++offset) {
    class->clone.data2[offset] = read_uint64(fd);
  }

  class->num_subclasses = -1;
  class->subclasses     = NULL;

  return 1;
}

void layer_aread_classes(FILE *fd, layer *layer) {
  layer->num_classes = read_uint64(fd);
  
  layer->classes = malloc(layer->num_classes * sizeof(struct class));
  assert(layer->classes != NULL);
  for(int j = 0; j < layer->num_classes; ++j) {
    class * class = layer->classes + j;
    class_read(fd, class);
  }

  /* test EOF */
  char c;
  assert(fread(&c, 1, 1, fd) == 0);
}

void layer_aread_connections(FILE *fd, layer *layer) {
  assert(layer->num_classes == read_uint64(fd));
  for(int class_id = 0; class_id < layer->num_classes; ++class_id) {
    class *class = &layer->classes[class_id];
    class->id.layer_id = read_uint64(fd);
    class->id.class_id = read_uint64(fd);
    
    class->num_subclasses = read_uint64(fd);
    class->subclasses = malloc(class->num_subclasses * sizeof(struct class_id));
    assert(class->subclasses != NULL);
    for(int j = 0; j < class->num_subclasses; ++j) {
      class->subclasses[j].layer_id = read_uint64(fd);
      class->subclasses[j].class_id = read_uint64(fd);
    }
  }

  /* test EOF */
  char c;
  assert(fread(&c, 1, 1, fd) == 0);
}

void lattice_read(int num_layers, const char *dir_clones, const char *dir_connections, lattice *lattice) {
  lattice->num_layers = num_layers;
  lattice->layers = malloc(num_layers * sizeof(layer));
  assert(lattice->layers != NULL);

  layer *layer = lattice->layers;
  for(int layer_id = 1; layer_id <= num_layers; ++layer_id) {
    char *fname_classes;
    asprintf(&fname_classes, "%s/%d.bin", dir_clones, layer_id);
    FILE *fd_classes = fopen(fname_classes, "rb");
    assert(fd_classes != NULL);

    char *fname_connections;
    asprintf(&fname_connections, "%s/%d.bin", dir_connections, layer_id);
    FILE *fd_connections = fopen(fname_connections, "rb");
    assert(fd_connections != NULL);

    layer_aread_classes(fd_classes, layer);
    layer_aread_connections(fd_connections, layer);

    free(fname_classes);
    free(fname_connections);
    fclose(fd_classes);
    fclose(fd_connections);
    ++layer;
  }
}
